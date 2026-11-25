/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The signature of a path: iterated integrals, Chen's identity, piecewise-linear paths

A path `X : ℝ → ℝ^ι` with locally integrable velocity `v i = dXⁱ/dt` (so `X` is absolutely
continuous, `Xⁱ_t = Xⁱ_s + ∫_s^t v i`) has, for every word `w = (i₁, …, i_k)` in the letters
`ι`, the iterated integral

`S(X)^{i₁…i_k}_{s,t} = ∫_{s < t₁ < ⋯ < t_k < t} dX^{i₁}_{t₁} ⋯ dX^{i_k}_{t_k}`,

defined recursively by `S^∅ = 1` and `S^{w i}_{s,t} = ∫_s^t S^w_{s,u} dXⁱ_u`
(Chevyrev–Kormilitzin, *A primer on the signature method in machine learning*,
arXiv:1603.03788v2, §1.2.1, equation (3) and Definition 1.4). The family of all these numbers
is the signature of `X` over `[s, t]`; we index it by words `List ι` and describe the path by its
velocity `v : ι → ℝ → ℝ`.

We prove Chen's identity (primer, Theorem 1.17) in the coordinate form, the signature of a linear
segment (the exponential of its increment, primer Example 1.20 and equation (17)) and the
signature of a piecewise-linear path as an ordered product of exponentials (primer,
Corollary 1.23), with the product of tensor series written out coefficientwise.
-/

open MeasureTheory intervalIntegral

@[expose] public section

namespace MathlibExt.Analysis.PathSignature

variable {ι : Type*}

/-- **Signature of a path (iterated integrals).** For a path in `ℝ^ι` with velocity
`v i = dXⁱ/dt`, `signature v s t w` is the iterated integral
`S(X)^{i₁…i_k}_{s,t} = ∫_{s<t₁<⋯<t_k<t} dX^{i₁}_{t₁} ⋯ dX^{i_k}_{t_k}` along the word
`w = [i₁, …, i_k]`, defined recursively by `S^∅_{s,t} = 1` and
`S^{w i}_{s,t} = ∫_s^t S^w_{s,u} dXⁱ_u = ∫_s^t S^w_{s,u} vⁱ(u) du`. The signature of the path
over `[s, t]` is the family `w ↦ signature v s t w` (Chevyrev and Kormilitzin, *A primer on the
signature method in machine learning*, arXiv:1603.03788v2, equation (3) and Definition 1.4). -/
noncomputable def signature (v : ι → ℝ → ℝ) (s t : ℝ) (w : List ι) : ℝ :=
  go w.reverse t
where
  /- The iterated integrals indexed by reversed words: `go (i :: l) t` integrates the iterated
  integral of the reversed word `l` against `dXⁱ`. -/
  go : List ι → ℝ → ℝ
    | [], _ => 1
    | i :: l, t => ∫ u in s..t, go l u * v i u

variable {v : ι → ℝ → ℝ}

/-- **Zeroth term of the signature.** The term of the empty word is `1` (Chevyrev and
Kormilitzin, arXiv:1603.03788v2, Definition 1.4: `S(X)^∅_{a,b} = 1`). -/
@[simp] theorem signature_nil (v : ι → ℝ → ℝ) (s t : ℝ) : signature v s t [] = 1 := by
  simp [signature, signature.go]

/-- **Recursive definition of the signature.** Appending a letter `i` to a word integrates
against `dXⁱ`: `S^{w i}_{s,t} = ∫_s^t S^w_{s,u} vⁱ(u) du` (Chevyrev and Kormilitzin,
arXiv:1603.03788v2, §1.2.1, the recursion before equation (3)). -/
theorem signature_concat (v : ι → ℝ → ℝ) (s t : ℝ) (w : List ι) (i : ι) :
    signature v s t (w ++ [i]) = ∫ u in s..t, signature v s u w * v i u := by
  simp [signature, signature.go]

/-- **First level of the signature is the increment.** `S^i_{s,t} = ∫_s^t vⁱ = Xⁱ_t − Xⁱ_s`
(Chevyrev and Kormilitzin, arXiv:1603.03788v2, equation (1)). -/
theorem signature_singleton (v : ι → ℝ → ℝ) (s t : ℝ) (i : ι) :
    signature v s t [i] = ∫ u in s..t, v i u := by
  simpa using signature_concat v s t [] i

/-- **Signature of a path over a trivial interval.** `S^w_{t,t}` is `1` for the empty word and `0`
for every nonempty word. -/
theorem signature_self (v : ι → ℝ → ℝ) (t : ℝ) (w : List ι) :
    signature v t t w = if w = [] then 1 else 0 := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w i _ => simp [signature_concat]

/-- **Continuity of the iterated integrals in the upper endpoint.** If every velocity component
is interval integrable on every interval, then `t ↦ S^w_{s,t}` is continuous for every word `w`. -/
theorem continuous_signature (hv : ∀ i a b, IntervalIntegrable (v i) volume a b) (s : ℝ)
    (w : List ι) : Continuous fun t => signature v s t w := by
  induction w using List.reverseRecOn with
  | nil => simpa using continuous_const
  | append_singleton w i ih =>
    simp only [signature_concat]
    exact intervalIntegral.continuous_primitive
      (fun a b => (hv i a b).continuousOn_mul ih.continuousOn) s

/-- **Integrability of the integrand of the signature recursion.** The integrand
`u ↦ S^w_{s,u} vⁱ(u)` of the recursion is interval integrable on every interval
when the velocity is. -/
theorem intervalIntegrable_signature_mul (hv : ∀ i a b, IntervalIntegrable (v i) volume a b)
    (s : ℝ) (w : List ι) (i : ι) (a b : ℝ) :
    IntervalIntegrable (fun u => signature v s u w * v i u) volume a b :=
  (hv i a b).continuousOn_mul (continuous_signature hv s w).continuousOn

/-- **The signature solves `dS = S ⊗ dX`.** For a path with continuous velocity, each iterated
integral is differentiable in its upper endpoint, with
`d/dt S^{w i}_{s,t} = S^w_{s,t} vⁱ(t)`: in coordinates, `t ↦ S(X)_{s,t}` solves the linear
controlled differential equation `dS_{s,t} = S_{s,t} ⊗ dX_t`, `S_{s,s} = 1`, the "universal
non-commutative exponential" (T. Lyons, *Rough paths, signatures and the modelling of functions on
streams*, Proc. ICM 2014, arXiv:1405.4537, Lemma 4.6). -/
theorem hasDerivAt_signature_concat (hv : ∀ i, Continuous (v i)) (s : ℝ) (w : List ι) (i : ι)
    (t : ℝ) :
    HasDerivAt (fun t => signature v s t (w ++ [i])) (signature v s t w * v i t) t := by
  have hw : Continuous fun t => signature v s t w :=
    continuous_signature (fun i a b => (hv i).intervalIntegrable a b) s w
  simp only [signature_concat]
  exact ((hw.mul (hv i)).integral_hasStrictDerivAt s t).hasDerivAt

/-- **Signature along a repeated letter.** For a path whose `i`-th velocity component is
continuous, the iterated integral along the word `i i ⋯ i` (`k` letters) is
`S^{i…i}_{s,t} = (Xⁱ_t − Xⁱ_s)^k / k!`, where `Xⁱ_t − Xⁱ_s = ∫_s^t vⁱ`. In particular the
signature of a one-dimensional path depends only on its increment (Chevyrev and Kormilitzin,
*A primer on the signature method in machine learning*, arXiv:1603.03788v2, Example 1.6). -/
theorem signature_replicate {i : ι} (hv : Continuous (v i)) (s t : ℝ) (k : ℕ) :
    signature v s t (List.replicate k i) = (∫ u in s..t, v i u) ^ k / k.factorial := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ', signature_concat]
    simp_rw [ih]
    set F : ℝ → ℝ := fun u => ∫ x in s..u, v i x
    have hF : ∀ u, HasDerivAt F (v i u) u := fun u =>
      ((hv).integral_hasStrictDerivAt s u).hasDerivAt
    have hderiv : ∀ x ∈ Set.uIcc s t, HasDerivAt (fun u => F u ^ (k + 1) / (k + 1).factorial)
        (F x ^ k / k.factorial * v i x) x := by
      intro x _
      have := ((hF x).pow (k + 1)).div_const ((k + 1).factorial : ℝ)
      convert this using 1
      rw [Nat.factorial_succ, Nat.cast_mul]
      have : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
    have hcont : Continuous fun u => F u ^ k / k.factorial * v i u :=
      (((continuous_primitive (fun a b => hv.intervalIntegrable a b) s).pow k).div_const _).mul hv
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable s t)]
    simp [F]

-- Splitting a sum over the words of length `k + 1` by the last letter; a helper for
-- `LinearCDE` and `RoughPath`, deliberately without a docstring (no page).
theorem sum_fin_succ_ofFn [Fintype ι] {M : Type*} [AddCommMonoid M] (k : ℕ)
    (F : List ι → M) :
    ∑ g : Fin (k + 1) → ι, F (List.ofFn g) = ∑ i, ∑ g : Fin k → ι, F (List.ofFn g ++ [i]) := by
  rw [← (Fin.snocEquiv (fun _ => ι)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun g _ => ?_
  congr 1
  rw [List.ofFn_succ']
  simp [Fin.snocEquiv, Fin.snoc_castSucc, Fin.snoc_last]

/-- **Chen's identity.** For a path whose velocity is interval integrable on every interval, and
all reals `a, b, c`, every iterated integral over `[a, c]` splits along `b`:
`S^{i₁…i_k}_{a,c} = ∑_{m=0}^{k} S^{i₁…i_m}_{a,b} · S^{i_{m+1}…i_k}_{b,c}`
(Chevyrev and Kormilitzin, *A primer on the signature method in machine learning*,
arXiv:1603.03788v2, Theorem 1.17, equation (19), stated there for `a < b < c`; the oriented
integrals make it hold for all `a, b, c`). Equivalently, `S(X)_{a,c} = S(X)_{a,b} ⊗ S(X)_{b,c}`
in the algebra of tensor series (Theorem 1.22), see `signature_eq_tensorMul`. -/
theorem signature_chen (hv : ∀ i a b, IntervalIntegrable (v i) volume a b) (a b c : ℝ)
    (w : List ι) :
    signature v a c w = ∑ m ∈ Finset.range (w.length + 1),
      signature v a b (w.take m) * signature v b c (w.drop m) := by
  induction w using List.reverseRecOn generalizing c with
  | nil => simp
  | append_singleton w i ih =>
    rw [signature_concat, ← integral_add_adjacent_intervals
      (intervalIntegrable_signature_mul hv a w i a b)
      (intervalIntegrable_signature_mul hv a w i b c), ← signature_concat]
    have hsplit : ∀ u, signature v a u w * v i u = ∑ m ∈ Finset.range (w.length + 1),
        signature v a b (w.take m) * (signature v b u (w.drop m) * v i u) := by
      intro u
      rw [ih u, Finset.sum_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    simp_rw [hsplit]
    rw [intervalIntegral.integral_finsetSum fun m _ =>
      (intervalIntegrable_signature_mul hv b (w.drop m) i b c).const_mul _]
    simp_rw [intervalIntegral.integral_const_mul, ← signature_concat]
    have hlast : signature v a b ((w ++ [i]).take (w.length + 1)) *
        signature v b c ((w ++ [i]).drop (w.length + 1)) = signature v a b (w ++ [i]) := by
      rw [List.take_of_length_le (by simp), List.drop_of_length_le (by simp)]
      simp
    have hbody : ∀ m ∈ Finset.range (w.length + 1),
        signature v a b ((w ++ [i]).take m) * signature v b c ((w ++ [i]).drop m) =
          signature v a b (w.take m) * signature v b c (w.drop m ++ [i]) := by
      intro m hm
      have hm' : m ≤ w.length := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      rw [List.take_append_of_le_length hm', List.drop_append_of_le_length hm']
    rw [List.length_append, List.length_singleton, Finset.sum_range_succ _ (w.length + 1), hlast,
      Finset.sum_congr rfl hbody, add_comm]

/-- **Product of tensor series, coefficientwise.** For coefficient families `F G : List ι → ℝ`
(tensor series `∑_w F(w) e_w`), the concatenation product has coefficients
`(F ⊗ G)(i₁…i_k) = ∑_{m=0}^{k} F(i₁…i_m) G(i_{m+1}…i_k)` (Chevyrev and Kormilitzin,
arXiv:1603.03788v2, Definition 1.19 and equation (20)). -/
noncomputable def tensorMul (F G : List ι → ℝ) (w : List ι) : ℝ :=
  ∑ m ∈ Finset.range (w.length + 1), F (w.take m) * G (w.drop m)

/-- **Unit tensor series.** The unit tensor series `1`: coefficient `1` on the empty word and `0`
elsewhere (Chevyrev and Kormilitzin, arXiv:1603.03788v2, Remark 1.26). -/
def tensorOne (w : List ι) : ℝ := if w = [] then 1 else 0

/-- **Chen's identity, algebraic form.** `S(X)_{a,c} = S(X)_{a,b} ⊗ S(X)_{b,c}` as tensor series
(Chevyrev and Kormilitzin, arXiv:1603.03788v2, Theorem 1.22, which the paper notes has the same
content as Theorem 1.17). -/
theorem signature_eq_tensorMul (hv : ∀ i a b, IntervalIntegrable (v i) volume a b)
    (a b c : ℝ) :
    signature v a c = tensorMul (signature v a b) (signature v b c) :=
  funext fun w => signature_chen hv a b c w

/-- **Exponential of a vector in the tensor series algebra.** For `x ∈ ℝ^ι`, the coefficient of
`e_{i₁} ⋯ e_{i_k}` in `exp(x) = ∑_k x^{⊗k}/k!` is `x_{i₁} ⋯ x_{i_k} / k!`
(Chevyrev and Kormilitzin, arXiv:1603.03788v2, Example 1.20). -/
noncomputable def tensorExp (x : ι → ℝ) (w : List ι) : ℝ :=
  (w.map x).prod / w.length.factorial

/-- **Exponential of a scaled vector, coefficientwise.**
`tensorExp (c • x) w = c ^ |w| · tensorExp x w`: the coefficient of `exp(c x)` at a word of length
`k` is `c^k` times that of `exp(x)`. -/
theorem tensorExp_smul (c : ℝ) (x : ι → ℝ) (w : List ι) :
    tensorExp (c • x) w = c ^ w.length * tensorExp x w := by
  unfold tensorExp
  have : (w.map (c • x)).prod = c ^ w.length * (w.map x).prod := by
    induction w with
    | nil => simp
    | cons i w ih => simp [ih, pow_succ]; ring
  rw [this, mul_div_assoc]

private theorem signature_of_eqOn_Ioc_aux (x : ι → ℝ) {s t : ℝ}
    (h : ∀ i, ∀ u ∈ Set.Ioc s t, v i u = x i) (w : List ι) :
    ∀ t' ∈ Set.Icc s t, signature v s t' w = (t' - s) ^ w.length * tensorExp x w := by
  induction w using List.reverseRecOn with
  | nil => intro t' _; simp [tensorExp]
  | append_singleton w i ih =>
    intro t' ht'
    rw [signature_concat]
    have hcongr : ∫ u in s..t', signature v s u w * v i u =
        ∫ u in s..t', (u - s) ^ w.length * (tensorExp x w * x i) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun u hu => ?_)
      rw [Set.uIoc_of_le ht'.1] at hu
      rw [ih u ⟨hu.1.le, hu.2.trans ht'.2⟩, h i u ⟨hu.1, hu.2.trans ht'.2⟩]
      ring
    rw [hcongr, intervalIntegral.integral_mul_const, intervalIntegral.integral_comp_sub_right
      (fun u => u ^ w.length), sub_self, integral_pow]
    simp only [tensorExp, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, List.length_append, List.length_singleton,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have h1 : ((w.length.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring

/-- **Signature of a linear segment is the exponential of its increment.** If the velocity is
constant, `v i u = x i` for `u ∈ (s, t]` and `s ≤ t`, then the path is linear on `[s, t]` with
increment `X_t − X_s = (t − s) x` and `S^w_{s,t} = (t − s)^{|w|} x_{i₁} ⋯ x_{i_k} / k!`, the
coefficient of `exp((t − s) x)` (Chevyrev and Kormilitzin, *A primer on the signature method in
machine learning*, arXiv:1603.03788v2, Example 1.20 and equation (17)). -/
theorem signature_of_eqOn_Ioc (x : ι → ℝ) {s t : ℝ} (hst : s ≤ t)
    (h : ∀ i, ∀ u ∈ Set.Ioc s t, v i u = x i) :
    signature v s t = tensorExp ((t - s) • x) := by
  funext w
  rw [tensorExp_smul]
  exact signature_of_eqOn_Ioc_aux x h w t ⟨hst, le_rfl⟩

/-- **Signature of a piecewise-linear path.** Let `τ₀ ≤ τ₁ ≤ ⋯` and let the velocity equal the
constant `x j` on each piece `(τ_j, τ_{j+1}]`, so the path is linear on `[τ_j, τ_{j+1}]` with
increment `Δ_j = (τ_{j+1} − τ_j) x j`. If the velocity is interval integrable on every interval,
then for every `n`,
`S(X)_{τ₀,τ_n} = exp(Δ₀) ⊗ exp(Δ₁) ⊗ ⋯ ⊗ exp(Δ_{n−1})`
(Chevyrev and Kormilitzin, *A primer on the signature method in machine learning*,
arXiv:1603.03788v2, Corollary 1.23, stated there for the unit grid `τ_j = j`). -/
theorem signature_piecewise_linear (hv : ∀ i a b, IntervalIntegrable (v i) volume a b)
    (τ : ℕ → ℝ) (hτ : Monotone τ) (x : ℕ → ι → ℝ)
    (h : ∀ j i, ∀ u ∈ Set.Ioc (τ j) (τ (j + 1)), v i u = x j i) (n : ℕ) :
    signature v (τ 0) (τ n) = ((List.range n).map fun j =>
      tensorExp ((τ (j + 1) - τ j) • x j)).foldl tensorMul tensorOne := by
  induction n with
  | zero => funext w; simp [signature_self, tensorOne]
  | succ n ih =>
    rw [signature_eq_tensorMul hv (τ 0) (τ n) (τ (n + 1)), ih,
      signature_of_eqOn_Ioc (x n) (hτ (Nat.le_succ n)) (h n), List.range_succ, List.map_append,
      List.foldl_append]
    rfl

/-- **Reparametrisation invariance of the signature.** Let the velocity `v` be continuous and let
`ψ : ℝ → ℝ` be differentiable with continuous derivative `ψ'`. The reparametrised path
`X̃_u = X_{ψ(u)}` has velocity `ṽⁱ(u) = vⁱ(ψ(u)) ψ'(u)`, and for all `s, t` and every word,
`S(X̃)^w_{s,t} = S(X)^w_{ψ(s),ψ(t)}`. For an increasing reparametrisation of `[a, b]` onto itself
this is the invariance of the signature under time reparametrisation (Chevyrev and Kormilitzin,
*A primer on the signature method in machine learning*, arXiv:1603.03788v2, §1.3.1); the
statement holds for every continuously differentiable `ψ`, monotone or not. -/
theorem signature_comp (hv : ∀ i, Continuous (v i)) {ψ ψ' : ℝ → ℝ}
    (hψ : ∀ x, HasDerivAt ψ (ψ' x) x) (hψ' : Continuous ψ') (s t : ℝ) (w : List ι) :
    signature (fun i u => v i (ψ u) * ψ' u) s t w = signature v (ψ s) (ψ t) w := by
  induction w using List.reverseRecOn generalizing t with
  | nil => simp
  | append_singleton w i ih =>
    rw [signature_concat, signature_concat]
    simp_rw [ih]
    have hg : Continuous fun r => signature v (ψ s) r w * v i r :=
      (continuous_signature (fun i a b => (hv i).intervalIntegrable a b) (ψ s) w).mul (hv i)
    have h := intervalIntegral.integral_comp_mul_deriv (a := s) (b := t)
      (fun x _ => hψ x) hψ'.continuousOn hg
    simp only [Function.comp_def] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun u _ => by ring

/-- **Signature of the time-reversed path over a sub-interval.** For the time reversal
`←X_u = X_{a+b−u}` of a path, with velocity `←vⁱ(u) = −vⁱ(a + b − u)`, the iterated integrals of
`←X` from `a` to `t` are those of `X` from `b` back to `a + b − t`:
`S(←X)^w_{a,t} = S(X)^w_{b,a+b−t}` for every word `w` and every real `t`. -/
theorem signature_reverse_eq (v : ι → ℝ → ℝ) (a b t : ℝ) (w : List ι) :
    signature (fun i u => -v i (a + b - u)) a t w = signature v b (a + b - t) w := by
  induction w using List.reverseRecOn generalizing t with
  | nil => simp
  | append_singleton w i ih =>
    rw [signature_concat, signature_concat]
    simp_rw [ih]
    have h := intervalIntegral.integral_comp_sub_left
      (fun r => signature v b r w * -v i r) (a := a) (b := t) (a + b)
    rw [h, show a + b - a = b by ring, intervalIntegral.integral_symm]
    simp [mul_neg, intervalIntegral.integral_neg]

/-- **Time-reversed signature is the inverse.** For a path with locally integrable velocity and its
time reversal `←X_u = X_{a+b−u}` on `[a, b]` (velocity `←vⁱ(u) = −vⁱ(a + b − u)`),
`S(X)_{a,b} ⊗ S(←X)_{a,b} = 1` in the algebra of tensor series (Chevyrev and Kormilitzin,
*A primer on the signature method in machine learning*, arXiv:1603.03788v2, Theorem 1.25,
equation (21)). The proof here is Chen's identity at `b` together with
`S(←X)_{a,b} = S(X)_{b,a}` (`signature_reverse_eq`). -/
theorem tensorMul_signature_reverse (hv : ∀ i a b, IntervalIntegrable (v i) volume a b)
    (a b : ℝ) :
    tensorMul (signature v a b) (signature (fun i u => -v i (a + b - u)) a b) = tensorOne := by
  have hrev : signature (fun i u => -v i (a + b - u)) a b = signature v b a := by
    funext w
    rw [signature_reverse_eq, show a + b - b = a by ring]
  rw [hrev, ← signature_eq_tensorMul hv a b a]
  funext w
  rw [signature_self, tensorOne]

/-- **Lower-endpoint derivative of an iterated integral (its value).** The derivative of
`c ↦ S^u_{c,b}` at `c₀` for continuous velocity: `0` for the empty word and `−vⁱ(c₀) S^w_{c₀,b}`
for `u = i w` (see `hasDerivAt_signature_lower`). -/
noncomputable def lowerDeriv (v : ι → ℝ → ℝ) (b c₀ : ℝ) : List ι → ℝ
  | [] => 0
  | i :: w => -(v i c₀ * signature v c₀ b w)

private theorem hasDerivAt_signature_upper_self (hv : ∀ i, Continuous (v i)) (c₀ : ℝ)
    (q : List ι) (hq : q ≠ []) :
    HasDerivAt (fun c => signature v c₀ c q)
      ((if q.dropLast = [] then 1 else 0) * v (q.getLast hq) c₀) c₀ := by
  have h := hasDerivAt_signature_concat hv c₀ q.dropLast (q.getLast hq) c₀
  rw [List.dropLast_append_getLast hq, signature_self] at h
  exact h

/-- **Derivative of the signature in its lower endpoint.** For a path with continuous velocity,
`c ↦ S^{i w}_{c,b}` is differentiable with derivative `−vⁱ(c) S^w_{c,b}`, and `S^∅_{c,b} = 1` is
constant. Proved from Chen's identity at the moving point and the derivative in the upper
endpoint (`hasDerivAt_signature_concat`). -/
theorem hasDerivAt_signature_lower (hv : ∀ i, Continuous (v i)) (b c₀ : ℝ) (u : List ι) :
    HasDerivAt (fun c => signature v c b u) (lowerDeriv v b c₀ u) c₀ := by
  have hvi : ∀ i a b, IntervalIntegrable (v i) volume a b := fun i a b =>
    (hv i).intervalIntegrable a b
  induction h : u.length using Nat.strong_induction_on generalizing u with
  | _ k ih =>
  rcases u with _ | ⟨i, w⟩
  · simpa [lowerDeriv] using hasDerivAt_const c₀ (1 : ℝ)
  -- Chen's identity at the moving point `c`, solved for `S^u_{c,b}`.
  have hfun : (fun c => signature v c b (i :: w)) = fun c => signature v c₀ b (i :: w) -
      ∑ m ∈ Finset.range (i :: w).length,
        signature v c₀ c ((i :: w).take (m + 1)) * signature v c b ((i :: w).drop (m + 1)) := by
    funext c
    rw [signature_chen hvi c₀ c b, Finset.sum_range_succ']
    simp
  rw [hfun]
  have hterm : ∀ m ∈ Finset.range (i :: w).length, HasDerivAt
      (fun c => signature v c₀ c ((i :: w).take (m + 1)) *
        signature v c b ((i :: w).drop (m + 1)))
      ((if ((i :: w).take (m + 1)).dropLast = [] then 1 else 0) *
          v (((i :: w).take (m + 1)).getLast (by simp)) c₀ *
          signature v c₀ b ((i :: w).drop (m + 1)) +
        signature v c₀ c₀ ((i :: w).take (m + 1)) *
          lowerDeriv v b c₀ ((i :: w).drop (m + 1))) c₀ := by
    intro m hm
    exact (hasDerivAt_signature_upper_self hv c₀ _ (by simp)).mul
      (ih _ (by simp at h ⊢; omega) _ rfl)
  refine ((hasDerivAt_const c₀ (signature v c₀ b (i :: w))).sub
    (HasDerivAt.fun_sum hterm)).congr_deriv ?_
  rw [Finset.sum_eq_single 0]
  · simp [lowerDeriv, signature_self]
  · intro m hm hm0
    have hw : w.take m ≠ [] := by
      simp only [List.length_cons, Finset.mem_range] at hm
      intro hnil
      rcases List.take_eq_nil_iff.mp hnil with h0 | h0
      · exact hm0 h0
      · subst h0; exact hm0 (by simpa using hm)
    have hnot : ¬ (i :: w.take m).dropLast = [] := by
      rw [List.dropLast_cons_of_ne_nil hw]
      simp
    simp [hnot, signature_self]
  · intro h0; simp at h0

/-- **First-letter recursion of the signature.** For a path with continuous velocity, the
iterated integral along `i w` is also `S^{i w}_{c,b} = ∫_c^b vⁱ(r) S^w_{r,b} dr`, integrating the
first letter last; together with the defining last-letter recursion this is the iterated-integral
formula `∫_{c<t₁<⋯<t_k<b}` read from either end. -/
theorem signature_cons (hv : ∀ i, Continuous (v i)) (c b : ℝ) (i : ι) (w : List ι) :
    signature v c b (i :: w) = ∫ r in c..b, v i r * signature v r b w := by
  have hcont : Continuous fun r => signature v r b w :=
    continuous_iff_continuousAt.2 fun r => (hasDerivAt_signature_lower hv b r w).continuousAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hasDerivAt_signature_lower hv b r (i :: w))
    (((hv i).mul hcont).neg.intervalIntegrable c b)
  simp only [lowerDeriv, intervalIntegral.integral_neg, signature_self, List.cons_ne_nil,
    ↓reduceIte] at h
  linarith

/-- **Reversing the orientation of the interval.** For a path with continuous velocity and all
reals `a, b`, `S(X)^{i₁…i_k}_{b,a} = (−1)^k S(X)^{i_k…i₁}_{a,b}`. -/
theorem signature_swap (hv : ∀ i, Continuous (v i)) (a b : ℝ) (w : List ι) :
    signature v b a w = (-1) ^ w.length * signature v a b w.reverse := by
  induction w using List.reverseRecOn generalizing a with
  | nil => simp
  | append_singleton w i ih =>
    rw [signature_concat, List.reverse_append, List.reverse_singleton, List.singleton_append,
      signature_cons hv, intervalIntegral.integral_symm]
    simp_rw [ih]
    rw [← intervalIntegral.integral_neg]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    simp only [List.length_append, List.length_singleton, pow_succ]
    ring

/-- **Time-reversed signature, coordinate form.** For a path with continuous velocity and its time
reversal `←X_u = X_{a+b−u}` on `[a, b]`,
`S(←X)^{i₁…i_k}_{a,b} = (−1)^k S(X)^{i_k…i₁}_{a,b}` (Chevyrev and Kormilitzin, *A primer on the
signature method in machine learning*, arXiv:1603.03788v2, Theorem 1.25, equation (22)). -/
theorem signature_reverse (hv : ∀ i, Continuous (v i)) (a b : ℝ) (w : List ι) :
    signature (fun i u => -v i (a + b - u)) a b w =
      (-1) ^ w.length * signature v a b w.reverse := by
  rw [signature_reverse_eq, show a + b - b = a by ring, signature_swap hv]

end MathlibExt.Analysis.PathSignature
