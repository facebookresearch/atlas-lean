/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Polynomial
import MathlibExt.Analysis.Distribution.GaussianSchwartz

/-!
# Hyperbolicity of Jensen polynomials

A quadratic log-ratio expansion gives eventual real-rootedness for the Jensen polynomials
of each fixed degree, by comparing their signs with those of a differentiated Gaussian.
-/

open Filter Asymptotics Polynomial Set
open scoped ContDiff Topology

namespace MetaMathlibExt
namespace eventually_jensen_hyperbolic_of_log_ratio_expansion

private lemma diff_hasDeriv {f g : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (g x) x)
    (d : ℕ) (h x : ℝ) :
    HasDerivAt ((fwdDiff h)^[d] f) ((fwdDiff h)^[d] g x) x := by
  induction d generalizing x with
  | zero => exact hf x
  | succ d ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change HasDerivAt (fun y => (fwdDiff h)^[d] f (y + h) - (fwdDiff h)^[d] f y)
      ((fwdDiff h)^[d] g (x + h) - (fwdDiff h)^[d] g x) x
    simpa only [Function.comp_def, id_eq, one_mul, mul_one] using
      (((ih (x + h)).comp x ((hasDerivAt_id x).add_const h)).fun_sub (ih x))

/-- Apply the mean value theorem once for each forward difference. -/
private lemma exists_diff_eq {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (d : ℕ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    ∃ z ∈ Icc x (x + d * h), (fwdDiff h)^[d] f x = h ^ d * iteratedDeriv d f z := by
  induction d generalizing x f with
  | zero => exact ⟨x, by simp, by simp⟩
  | succ d ih =>
    have H := diff_hasDeriv (fun y => (hf.differentiable (by simp) y).hasDerivAt) d h
    obtain ⟨c, hc, heq⟩ := exists_deriv_eq_slope ((fwdDiff h)^[d] f)
      (show x < x + h by linarith) (fun y _ => (H y).continuousAt.continuousWithinAt)
      (fun y _ => (H y).differentiableAt.differentiableWithinAt)
    obtain ⟨z, hz, hz'⟩ := ih (f := deriv f) (by simpa using hf.deriv') c
    refine ⟨z, ⟨hc.1.le.trans hz.1, ?_⟩, ?_⟩
    · push_cast
      linarith [hz.2, hc.2]
    · rw [(H c).deriv, add_sub_cancel_left] at heq
      rw [Function.iterate_succ_apply', iteratedDeriv_succ', fwdDiff,
        ← (eq_div_iff hh.ne').mp heq, hz', pow_succ]
      ring

private lemma smooth_partial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ → ℝ} (h : ContDiff ℝ ∞ (Function.uncurry F)) (d : ℕ) :
    ContDiff ℝ ∞ (fun p : E × ℝ => iteratedDeriv d (F p.1) p.2) := by
  induction d with
  | zero =>
    simp only [iteratedDeriv_zero]
    exact h
  | succ d ih =>
    let G (p : E × ℝ) (x : ℝ) := iteratedDeriv d (F p.1) x
    have hG : ContDiff ℝ ∞ (Function.uncurry G) :=
      ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
    simp only [iteratedDeriv_succ]
    exact hG.fderiv_apply (g := Prod.snd) contDiff_snd (k := fun _ => 1)
      contDiff_const (by simp)

private lemma diff_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ → ℝ} (hF : ContDiff ℝ ∞ (Function.uncurry F))
    {u : ℕ → E} {u₀ : E} (hu : Tendsto u atTop (𝓝 u₀))
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hδ0 : Tendsto δ atTop (𝓝 0)) (d : ℕ) :
    Tendsto (fun n => (fwdDiff (δ n))^[d] (F (u n)) 0 / δ n ^ d)
      atTop (𝓝 (iteratedDeriv d (F u₀) 0)) := by
  choose z hz he using fun n => exists_diff_eq
    (f := F (u n)) (hF.comp (contDiff_const.prodMk contDiff_id)) d (hδ n) 0
  have hz0 : Tendsto z atTop (𝓝 0) := squeeze_zero (fun n => (hz n).1)
    (fun n => by simpa using (hz n).2) (by simpa using hδ0.const_mul (d : ℝ))
  convert ((smooth_partial hF d).continuous.tendsto (u₀, 0)).comp (hu.prodMk_nhds hz0) using 1
  ext n
  simp [he, (hδ n).ne']

/-- Sample points in increasing order, starting with a positive value. -/
private def Alternates (d : ℕ) (f : ℝ → ℝ) (x : ℕ → ℝ) : Prop :=
  (∀ i < d, x i < x (i + 1)) ∧ ∀ i ≤ d, 0 < (-1 : ℝ) ^ i * f (x i)

/-- At either end, decay to zero supplies the extra interval for the mean value theorem. -/
private lemma alternates_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hlim : Tendsto f (cocompact ℝ) (𝓝 0)) {d : ℕ} {x : ℕ → ℝ} (hx : Alternates d f x) :
    ∃ y, Alternates (d + 1) (deriv f) y := by
  obtain ⟨a, ha, hfa⟩ := ((eventually_lt_atBot (x 0)).and
    ((hlim.mono_left atBot_le_cocompact).eventually_lt_const
      (by simpa using hx.2 0 (Nat.zero_le d)))).exists
  have htop : Tendsto (fun y => (-1 : ℝ) ^ d * f y) atTop (𝓝 0) := by
    simpa using (hlim.mono_left atTop_le_cocompact).const_mul ((-1 : ℝ) ^ d)
  obtain ⟨b, hb, hfb⟩ := ((eventually_gt_atTop (x d)).and
    (htop.eventually_lt_const (hx.2 d le_rfl))).exists
  let w : ℕ → ℝ
    | 0 => a
    | i + 1 => if i ≤ d then x i else b
  have hw (i : ℕ) (hi : i ≤ d + 1) : w i < w (i + 1) ∧
      0 < (-1 : ℝ) ^ i * (f (w (i + 1)) - f (w i)) := by
    cases i with
    | zero => simpa [w] using And.intro ha (sub_pos.mpr hfa)
    | succ i =>
      have hid : i ≤ d := by omega
      by_cases hil : i < d
      · simp only [w, ite_eq_left hid, ite_eq_left (Nat.succ_le_of_lt hil)]
        refine ⟨hx.1 i hil, ?_⟩
        have h1 := hx.2 i hid
        have h2 := hx.2 (i + 1) (by omega)
        rw [pow_succ] at h2 ⊢
        linarith only [h1, h2]
      · obtain rfl : i = d := by omega
        simp only [w, ite_eq_left le_rfl, Nat.not_succ_le_self, ite_false, pow_succ]
        exact ⟨hb, by linarith only [hfb]⟩
  have H (i : ℕ) (hi : i ≤ d + 1) : ∃ y ∈ Ioo (w i) (w (i + 1)),
      0 < (-1 : ℝ) ^ i * deriv f y := by
    obtain ⟨c, hc, he⟩ := exists_deriv_eq_slope f (hw i hi).1
      hf.continuous.continuousOn hf.differentiableOn
    refine ⟨c, hc, ?_⟩
    rw [he, ← mul_div_assoc]
    exact div_pos (hw i hi).2 (sub_pos.mpr (hw i hi).1)
  classical
  let y i := if hi : i ≤ d + 1 then (H i hi).choose else 0
  refine ⟨y, fun i hi => ?_, fun i hi => ?_⟩
  · simpa only [y, dite_eq_left hi.le, dite_eq_left (Nat.succ_le_of_lt hi)] using
      ((H i hi.le).choose_spec.1.2.trans (H (i + 1) (by omega)).choose_spec.1.1)
  · simpa only [y, dite_eq_left hi] using (H i hi).choose_spec.2

private lemma gaussian_signs (d : ℕ) : ∃ x,
    Alternates d (iteratedDeriv d (fun t : ℝ => Real.exp (-t ^ 2))) x := by
  obtain ⟨G, hG⟩ :=
    MathlibExt.Analysis.Distribution.GaussianSchwartzWanted.gaussian_mem_schwartz (E := ℝ)
  have hg : ⇑G = fun t : ℝ => Real.exp (-t ^ 2) := by
    funext t
    simpa [Real.norm_eq_abs] using hG t
  rw [← hg]
  have H (k : ℕ) : ∃ S : SchwartzMap ℝ ℝ, ⇑S = iteratedDeriv k (⇑G) := by
    induction k with
    | zero => exact ⟨G, by simp⟩
    | succ k ih =>
      obtain ⟨S, hS⟩ := ih
      exact ⟨SchwartzMap.derivCLM ℝ ℝ S, by rw [iteratedDeriv_succ, ← hS]; rfl⟩
  induction d with
  | zero => exact ⟨fun _ => 0, by simp [Alternates, hg]⟩
  | succ d ih =>
    obtain ⟨x, hx⟩ := ih
    obtain ⟨S, hS⟩ := H d
    rw [iteratedDeriv_succ, ← hS]
    exact alternates_deriv ((S.smooth 1).differentiable (by simp)) S.tendsto_cocompact
      (hS.symm ▸ hx)

private lemma count_roots {p : ℝ[X]} {d : ℕ} (hp : p.natDegree ≤ d)
    {f v : ℝ → ℝ} (hf : Continuous f) (hv : Function.Injective v)
    (hroot : ∀ t, f t = 0 → p.IsRoot (v t)) {x : ℕ → ℝ} (hx : Alternates d f x) :
    p.roots.card = p.natDegree := by
  classical
  by_cases hp0 : p = 0
  · simp [hp0]
  have H (i : Fin d) : ∃ t ∈ Ioo (x i) (x (i + 1 : ℕ)), f t = 0 := by
    let s := (-1 : ℝ) ^ (i : ℕ)
    have hpos : 0 < s * f (x i) := hx.2 i i.isLt.le
    have hneg : s * f (x (i + 1 : ℕ)) < 0 := by
      have hh := hx.2 (i + 1) (Nat.succ_le_of_lt i.isLt)
      rw [pow_succ] at hh
      dsimp [s]
      linarith
    obtain ⟨t, ht, he⟩ := intermediate_value_Ioo' (hx.1 _ i.isLt).le
      ((continuous_const.mul hf).continuousOn) (show 0 ∈ Ioo _ _ from ⟨hneg, hpos⟩)
    exact ⟨t, ht, (mul_eq_zero.mp he).resolve_left (by dsimp [s]; positivity)⟩
  choose t ht he using H
  have hmono : StrictMono (fun i : Fin (d + 1) => x i) :=
    Fin.strictMono_iff_lt_succ.mpr fun i => hx.1 _ i.isLt
  have htmono : StrictMono t := by
    intro i j hij
    exact (ht i).2.trans_le ((hmono.monotone (show i.succ ≤ j.castSucc from hij)).trans
      (ht j).1.le)
  let roots (i : Fin d) : p.roots.toFinset :=
    ⟨v (t i), Multiset.mem_toFinset.mpr ((mem_roots hp0).2 (hroot _ (he i)))⟩
  have hcard := Fintype.card_le_of_injective roots
    (fun i j h => htmono.injective (hv (congrArg Subtype.val h)))
  have hdistinct : d ≤ p.roots.toFinset.card := by simpa using hcard
  exact (card_roots' _).antisymm (hp.trans (hdistinct.trans p.roots.toFinset_card_le))

private noncomputable def weight (d k : ℕ) : ℝ := (-1) ^ (d - k) * d.choose k

/-- A perturbation of size little-o of the mesh to the order of the difference
does not change its normalized limit. -/
private lemma perturbed_diff_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ → ℝ} (hF : ContDiff ℝ ∞ (Function.uncurry F))
    {u : ℕ → E} {u₀ : E} (hu : Tendsto u atTop (𝓝 u₀))
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hδ0 : Tendsto δ atTop (𝓝 0)) (d : ℕ)
    (r : ℕ → ℕ → ℝ) (hr : ∀ k ≤ d, r k =o[atTop] fun n => δ n ^ d) :
    Tendsto (fun n => (∑ k ∈ Finset.range (d + 1),
      weight d k * F (u n) (k * δ n) * Real.exp (r k n)) / δ n ^ d)
      atTop (𝓝 (iteratedDeriv d (F u₀) 0)) := by
  have herr (k : ℕ) (hk : k ≤ d) :
      Tendsto (fun n => (Real.exp (r k n) - 1) / δ n ^ d) atTop (𝓝 0) := by
    have h0 := (hr k hk).tendsto_zero_of_tendsto (hδ0.pow d)
    have hO : (fun n => Real.exp (r k n) - 1) =O[atTop] r k := by
      simpa [Function.comp_def] using (Real.hasDerivAt_exp 0).isBigO_sub.comp_tendsto h0
    exact (hO.trans_isLittleO (hr k hk)).tendsto_div_nhds_zero
  have hterm (k : ℕ) (hk : k ∈ Finset.range (d + 1)) :
      Tendsto (fun n => weight d k * F (u n) (k * δ n) *
        ((Real.exp (r k n) - 1) / δ n ^ d)) atTop (𝓝 0) := by
    have hmesh : Tendsto (fun n => (k : ℝ) * δ n) atTop (𝓝 0) := by
      simpa using hδ0.const_mul (k : ℝ)
    have hval := (hF.continuous.tendsto (u₀, 0)).comp (hu.prodMk_nhds hmesh)
    simpa using (hval.const_mul (weight d k)).mul (herr k (Finset.mem_range_succ_iff.mp hk))
  have h := (diff_limit hF hu hδ hδ0 d).add (tendsto_finsetSum _ hterm)
  simp only [Finset.sum_const_zero, add_zero] at h
  apply h.congr
  intro n
  rw [fwdDiff_iter_eq_sum_shift, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, nsmul_eq_mul, zero_add, weight]
  ring

private noncomputable def jensen (α : ℕ → ℝ) (d n : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (d + 1), C ((d.choose k : ℝ) * α (n + k)) * X ^ k

private noncomputable def sample (a h t : ℝ) : ℝ := -Real.exp (-2 * t * h - a)

private noncomputable def normalized (α A δ : ℕ → ℝ) (d n : ℕ) (t : ℝ) : ℝ :=
  (-1) ^ d * Real.exp (-t ^ 2) * (jensen α d n).eval (sample (A n) (δ n) t) /
    α n / δ n ^ d

/-- Evaluation at a negative exponential turns the alternating binomial sum into a forward
difference of a translated Gaussian with a polynomial perturbation in its exponent. -/
private lemma normalized_limit {α A δ : ℕ → ℝ} (hα : ∀ n, 0 < α n)
    (hδ : ∀ n, 0 < δ n) (hδ0 : Tendsto δ atTop (𝓝 0)) (d : ℕ) (g : ℕ → ℕ → ℝ)
    (hg : ∀ j ∈ Finset.Icc 3 d, g j =o[atTop] fun n => δ n ^ j)
    (hexp : ∀ k ≤ d, (fun n => Real.log (α (n + k) / α n) -
        (A n * k - δ n ^ 2 * k ^ 2 + ∑ j ∈ Finset.Icc 3 d, g j n * (k : ℝ) ^ j)) =o[atTop]
      fun n => δ n ^ d) (t : ℝ) :
    Tendsto (fun n => normalized α A δ d n t) atTop
      (𝓝 (iteratedDeriv d (fun x : ℝ => Real.exp (-x ^ 2)) t)) := by
  let J := ↥(Finset.Icc 3 d)
  let u (n : ℕ) (j : J) := g j n / δ n ^ (j : ℕ)
  have hu : Tendsto u atTop (𝓝 0) :=
    tendsto_pi_nhds.mpr fun j => (hg j j.property).tendsto_div_nhds_zero
  let F (c : J → ℝ) (y : ℝ) := Real.exp (-(t + y) ^ 2 + ∑ j : J, c j * y ^ (j : ℕ))
  have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
    unfold Function.uncurry F
    fun_prop
  let r (k n : ℕ) := Real.log (α (n + k) / α n) -
    (A n * k - δ n ^ 2 * k ^ 2 + ∑ j ∈ Finset.Icc 3 d, g j n * (k : ℝ) ^ j)
  have H := perturbed_diff_limit hF hu hδ hδ0 d r hexp
  have hderiv : iteratedDeriv d (F 0) 0 =
      iteratedDeriv d (fun x : ℝ => Real.exp (-x ^ 2)) t := by
    have e : F 0 = fun y : ℝ => Real.exp (-(t + y) ^ 2) := by ext y; simp [F]
    simp only [e, iteratedDeriv_comp_const_add d (fun x : ℝ => Real.exp (-x ^ 2)) t, add_zero]
  rw [hderiv] at H
  apply H.congr
  intro n
  have hcoeff (k : ℕ) :
      F (u n) (k * δ n) * Real.exp (r k n) =
        Real.exp (-t ^ 2) * Real.exp (-2 * t * δ n - A n) ^ k * (α (n + k) / α n) := by
    have hsum : ∑ j : J, u n j * ((k : ℝ) * δ n) ^ (j : ℕ) =
        ∑ j ∈ Finset.Icc 3 d, g j n * (k : ℝ) ^ j := by
      rw [← Finset.sum_coe_sort (Finset.Icc 3 d) (fun j => g j n * (k : ℝ) ^ j)]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [u]
      rw [mul_pow]
      field_simp [(hδ n).ne']
    dsimp only [F]
    rw [hsum, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add,
      ← Real.exp_log (div_pos (hα (n + k)) (hα n)), ← Real.exp_add]
    congr 1
    dsimp [r]
    ring
  unfold normalized jensen sample
  simp only [eval_finsetSum, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd := Finset.mem_range_succ_iff.mp hk
  have hsign : (-1 : ℝ) ^ d * (-1) ^ k = (-1) ^ (d - k) := by
    rw [← pow_add, neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (d - k)]
    congr 1
    omega
  rw [mul_assoc, hcoeff, eval_mul, eval_C, eval_pow, eval_X, neg_pow, weight, ← hsign]
  ring

end eventually_jensen_hyperbolic_of_log_ratio_expansion

open eventually_jensen_hyperbolic_of_log_ratio_expansion in
set_option linter.unusedVariables false in
/-- **Hyperbolicity of Jensen polynomials from a log-ratio expansion.** Let $\alpha$, $A$ and
$\delta$ be sequences of positive real numbers indexed by $n \in \mathbb{N}$ with
$\delta(n) \to 0$, let $d \ge 1$ be an integer, and for $3 \le j \le d$ let $g_j$ be a real
sequence with $g_j(n) = o(\delta(n)^j)$ as $n \to \infty$. Suppose that for every natural number
$k \le d$,
$$
\log \frac{\alpha(n + k)}{\alpha(n)} = A(n) k - \delta(n)^2 k^2 + \sum_{j=3}^{d} g_j(n) k^j +
o(\delta(n)^d)
$$
as $n \to \infty$. Then for all sufficiently large $n$ the Jensen polynomial
$J_\alpha^{d,n}(X) = \sum_{j=0}^{d} \binom{d}{j} \alpha(n + j) X^j$ is hyperbolic: the number of
its real roots, counted with multiplicity, equals its degree.

The source also proves that suitably renormalized Jensen polynomials converge to the Hermite
polynomials; that conclusion is not part of this statement.

Source: Jashan Bal, Fern Haraldson, Joshua Males and Ian Thompson, *Jensen Polynomials Associated
with Wright's Circle Method: Hyperbolicity and Turán Inequalities*, INTEGERS 25 (2025),
Article A36, Theorem 5 (`integers-2025-A36-thm-5`), quoted there from Griffin, Ono, Rolen and
Zagier. -/
public theorem eventually_jensen_hyperbolic_of_log_ratio_expansion {α A δ : ℕ → ℝ}
    (hα : ∀ n, 0 < α n) (hA : ∀ n, 0 < A n) (hδ : ∀ n, 0 < δ n)
    (hδ0 : Tendsto δ atTop (nhds 0)) {d : ℕ} (hd : 1 ≤ d) (g : ℕ → ℕ → ℝ)
    (hg : ∀ j ∈ Finset.Icc 3 d, g j =o[atTop] fun n => δ n ^ j)
    (hexp : ∀ k ≤ d, (fun n => Real.log (α (n + k) / α n) -
        (A n * k - δ n ^ 2 * k ^ 2 + ∑ j ∈ Finset.Icc 3 d, g j n * (k : ℝ) ^ j)) =o[atTop]
      fun n => δ n ^ d) :
    ∀ᶠ n in atTop,
      (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) * α (n + j)) * X ^ j).roots.card =
        (∑ j ∈ Finset.range (d + 1), C ((d.choose j : ℝ) * α (n + j)) * X ^ j).natDegree := by
  obtain ⟨x, hx⟩ := gaussian_signs d
  have he (i : ℕ) (hi : i ≤ d) : ∀ᶠ n in atTop,
      0 < (-1 : ℝ) ^ i * normalized α A δ d n (x i) :=
    ((normalized_limit hα hδ hδ0 d g hg hexp (x i)).const_mul ((-1 : ℝ) ^ i)).eventually_const_lt
      (hx.2 i hi)
  have hall := (eventually_all_finset (Finset.range (d + 1))).mpr
    (fun i hi => he i (Finset.mem_range_succ_iff.mp hi))
  filter_upwards [hall] with n hn
  change (jensen α d n).roots.card = (jensen α d n).natDegree
  apply count_roots (d := d) (f := normalized α A δ d n) (v := sample (A n) (δ n)) (x := x)
  · apply natDegree_sum_le_of_forall_le
    intro i hi
    exact (natDegree_C_mul_le _ _).trans (by simpa using Finset.mem_range_succ_iff.mp hi)
  · unfold normalized sample
    fun_prop
  · intro s t heq
    have h : -2 * s * δ n - A n = -2 * t * δ n - A n :=
      Real.exp_injective (neg_injective heq)
    exact mul_right_cancel₀ (hδ n).ne' (show s * δ n = t * δ n by linarith)
  · intro t ht
    simpa [normalized, (hα n).ne', (hδ n).ne', IsRoot] using ht
  · exact ⟨hx.1, fun i hi => hn i (Finset.mem_range_succ_iff.mpr hi)⟩

end MetaMathlibExt
