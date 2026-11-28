/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Combinatorics.RandomSubset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorial.Basic

import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Kim–Vu polynomial concentration

Let `t₁, …, tₙ` be independent `{0, 1}` random variables with `E tᵢ = pᵢ` and let
`Y = ∑_{e ∈ E} w(e) ∏_{i ∈ e} tᵢ` be a polynomial with positive coefficients whose supporting
hypergraph `E` has edges of size at most `k`. For a set `A` of variables, the partial derivative
of `Y` with respect to `A` is `Y_A = ∑_{e ⊇ A} w(e) ∏_{i ∈ e \ A} tᵢ`. Let
`E_j = max_{|A| = j} E(Y_A)`, `E = max_{j ≥ 0} E_j` and `E' = max_{j ≥ 1} E_j`. Kim and Vu proved

`P(|Y - E Y| > a_k (E E')^{1/2} λ^k) = O(exp(-λ + (k - 1) log n))` for `λ > 1`,
`a_k = 8^k (k!)^{1/2}`.

The point is that only the *average* effects `E_j` of groups of variables enter, not their
worst-case effects as in Azuma's or McDiarmid's inequality. The model application is the number
of triangles in `G(n, p)` for `p` below `n^{-2/3}`, where the worst-case effect of an edge exceeds
the mean.

Reference: J. H. Kim and V. H. Vu, "Concentration of multivariate polynomials and its
applications", *Combinatorica* 20 (2000), 417–434, Section 1.2, Main Theorem.
-/

@[expose] public section

open Finset MeasureTheory ProbabilityTheory unitInterval
open MathlibExt.Probability.Combinatorics.RandomSubset

namespace MathlibExt.Probability.KimVuConcentrationWanted

variable {n : ℕ}

/-- **Partial derivative of a positive polynomial.** For a weighted hypergraph on `Fin n` with
edge set `E` and weights `w`, and a set `A` of variables, the value at `ω` of
`Y_{H_A} = ∑_{e ∈ E, A ⊆ e} w(e) ∏_{i ∈ e \ A} tᵢ`, where `tᵢ = 1` if `ω i` and `0` otherwise.
For `A = ∅` this is the polynomial `Y_H` itself (J. H. Kim and V. H. Vu, "Concentration of
multivariate polynomials and its applications", *Combinatorica* 20 (2000), Section 1.2, the
truncated subhypergraph `H_A`). -/
noncomputable def truncatedPoly (E : Finset (Finset (Fin n))) (w : Finset (Fin n) → ℝ)
    (A : Finset (Fin n)) (ω : Fin n → Bool) : ℝ :=
  ∑ e ∈ E with A ⊆ e, w e * ∏ i ∈ e \ A, (if ω i then (1 : ℝ) else 0)

/-- **Maximal average effect of `j` variables.** `E_j(H) = max_{|A| = j} E(Y_{H_A})`, the
expectation taken for independent `{0, 1}` variables `tᵢ` with means `p i`; it is `0` when
`j > n` (J. H. Kim and V. H. Vu, *Combinatorica* 20 (2000), Section 1.2). -/
noncomputable def maxAverageEffect (p : Fin n → I) (E : Finset (Finset (Fin n)))
    (w : Finset (Fin n) → ℝ) (j : ℕ) : ℝ :=
  ⨆ A : {A : Finset (Fin n) // A.card = j},
    ∫ ω, truncatedPoly E w A.1 ω ∂(randomSubsetLaw p)
private abbrev Bits (n : ℕ) := Fin n → Bool

private def bit (ω : Bits n) (i : Fin n) : ℝ := if ω i then 1 else 0

private theorem bit_nonneg (ω : Bits n) (i : Fin n) : 0 ≤ bit ω i := by
  unfold bit
  split <;> norm_num

private theorem prod_bit_eq_indicator (A : Finset (Fin n)) (ω : Bits n) :
    (∏ i ∈ A, bit ω i) = (containsEvent A).indicator 1 ω := by
  by_cases h : ω ∈ containsEvent A
  · rw [Set.indicator_of_mem h, Finset.prod_eq_one]
    · rfl
    · intro i hi
      simp [bit, h i hi]
  · rw [Set.indicator_of_notMem h]
    simp only [containsEvent, Set.mem_ofPred_eq, not_forall] at h
    obtain ⟨i, hi, hω⟩ := h
    exact Finset.prod_eq_zero hi (by simp [bit, hω])

private theorem integral_prod_bit (p : Fin n → I) (A : Finset (Fin n)) :
    (∫ ω, ∏ i ∈ A, bit ω i ∂(randomSubsetLaw p)) = ∏ i ∈ A, (p i : ℝ) := by
  simp_rw [prod_bit_eq_indicator]
  rw [integral_indicator_one (measurableSet_containsEvent A), randomSubsetLaw_real_containsEvent]

/-- The terms have their own indices, allowing several terms to use the same monomial. -/
private noncomputable def poly {ι : Type} (S : Finset ι) (edge : ι → Finset (Fin n))
    (w : ι → ℝ) (ω : Bits n) : ℝ :=
  ∑ a ∈ S, w a * ∏ i ∈ edge a, bit ω i

private noncomputable def effectTerm (p : Fin n → I) (e A : Finset (Fin n)) (x : ℝ) : ℝ :=
  if A ⊆ e then x * ∏ i ∈ e \ A, (p i : ℝ) else 0

private noncomputable def effect {ι : Type} (p : Fin n → I) (S : Finset ι)
    (edge : ι → Finset (Fin n)) (w : ι → ℝ) (A : Finset (Fin n)) : ℝ :=
  ∑ a ∈ S, effectTerm p (edge a) A (w a)

private theorem effectTerm_nonneg (p : Fin n → I) (e A : Finset (Fin n))
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ effectTerm p e A x := by
  unfold effectTerm
  split
  · exact mul_nonneg hx (Finset.prod_nonneg fun i _ => (p i).2.1)
  · exact le_rfl

private theorem effect_nonneg {ι : Type} (p : Fin n → I) (S : Finset ι)
    (edge : ι → Finset (Fin n)) (w : ι → ℝ) (hw : ∀ a ∈ S, 0 ≤ w a) (A : Finset (Fin n)) :
    0 ≤ effect p S edge w A :=
  Finset.sum_nonneg fun a ha => effectTerm_nonneg p _ _ (hw a ha)

private theorem integral_truncatedPoly (p : Fin n → I) (E : Finset (Finset (Fin n)))
    (w : Finset (Fin n) → ℝ) (A : Finset (Fin n)) :
    (∫ ω, truncatedPoly E w A ω ∂(randomSubsetLaw p)) = effect p E id w A := by
  unfold truncatedPoly effect
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite), Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : A ⊆ e <;> simp only [effectTerm, id_eq, h, ite_true, ite_false]
  rw [integral_const_mul, ← integral_prod_bit]
  rfl

private theorem integral_poly {ι : Type} (p : Fin n → I) (S : Finset ι)
    (edge : ι → Finset (Fin n)) (w : ι → ℝ) :
    (∫ ω, poly S edge w ω ∂(randomSubsetLaw p)) = effect p S edge w ∅ := by
  unfold poly effect
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_const_mul, integral_prod_bit]
  simp [effectTerm]

private theorem tail_of_exp (p : Fin n → I) (f : Bits n → ℝ) (c : ℝ)
    (h : (∫ ω, Real.exp (f ω) ∂(randomSubsetLaw p)) ≤ 1) :
    (randomSubsetLaw p).real {ω | c ≤ f ω} ≤ Real.exp (-c) := by
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := randomSubsetLaw p) (f := fun ω => Real.exp (f ω))
    (ae_of_all _ fun ω => (Real.exp_pos (f ω)).le) Integrable.of_finite (Real.exp c)
  rw [Real.exp_neg, ← one_div, le_div_iff₀' (Real.exp_pos c)]
  simpa only [Real.exp_le_exp] using hmarkov.trans h

private theorem integral_select (p : Fin n → I) (i : Fin n) (f g : Bits n → ℝ)
    (hf : ∀ ω ω', (∀ j, j ≠ i → ω j = ω' j) → f ω = f ω')
    (hg : ∀ ω ω', (∀ j, j ≠ i → ω j = ω' j) → g ω = g ω') :
    (∫ ω, (if ω i then f ω else g ω) ∂(randomSubsetLaw p)) =
      (p i : ℝ) * (∫ ω, f ω ∂(randomSubsetLaw p)) +
        (1 - (p i : ℝ)) * (∫ ω, g ω ∂(randomSubsetLaw p)) := by
  classical
  let R := Finset.univ.erase i
  let restrict (ω : Bits n) (j : R) := ω j
  let extend (r : R → Bool) (j : Fin n) :=
    if hj : j = i then false else r ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩
  have hind : iIndepFun (fun j (ω : Bits n) => ω j) (randomSubsetLaw p) :=
    iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have hdisj : Disjoint ({i} : Finset (Fin n)) R := by simp [R]
  have hind' : IndepFun (fun ω : Bits n => ω i) restrict (randomSubsetLaw p) :=
    (hind.indepFun_finset {i} R hdisj (fun j => measurable_pi_apply j)).comp
      (measurable_pi_apply (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset (Fin n))))
      measurable_id
  have factor (h : Bits n → ℝ)
      (hh : ∀ ω ω', (∀ j, j ≠ i → ω j = ω' j) → h ω = h ω')
      (b : ℝ → ℝ) :
      (∫ ω, b (bit ω i) * h ω ∂(randomSubsetLaw p)) =
        (∫ ω, b (bit ω i) ∂(randomSubsetLaw p)) *
          (∫ ω, h ω ∂(randomSubsetLaw p)) := by
    have heq : (fun ω => (h ∘ extend) (restrict ω)) = h := by
      funext ω
      exact (hh _ _ fun j hj => by simp [extend, restrict, hj])
    have hi := hind'.comp
      (show Measurable (fun x : Bool => b (if x then 1 else 0)) from measurable_of_finite _)
      (measurable_of_finite (h ∘ extend))
    exact heq ▸ hi.integral_mul_eq_mul_integral
      (measurable_of_finite _).aestronglyMeasurable (measurable_of_finite _).aestronglyMeasurable
  have ht : (∫ ω, bit ω i ∂(randomSubsetLaw p)) = (p i : ℝ) := by
    simpa using integral_prod_bit p {i}
  have hfalse : (∫ ω, 1 - bit ω i ∂(randomSubsetLaw p)) = 1 - (p i : ℝ) := by
    rw [integral_sub Integrable.of_finite Integrable.of_finite, ht, integral_const]
    simp
  have heq (ω : Bits n) :
      (if ω i then f ω else g ω) = bit ω i * f ω + (1 - bit ω i) * g ω := by
    cases hω : ω i <;> simp [bit, hω]
  simp_rw [heq]
  have hf' := factor f hf id
  simp only [id_eq] at hf'
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    hf', factor g hg (fun x => 1 - x), ht, hfalse]

private theorem bernoulli_exp (q : I) {t : ℝ} (ht : |t| ≤ 1) :
    (q : ℝ) * Real.exp (t * (1 - (q : ℝ)) - t ^ 2 * (q : ℝ)) +
      (1 - (q : ℝ)) * Real.exp (t * (0 - (q : ℝ)) - t ^ 2 * (q : ℝ)) ≤ 1 := by
  have hq := q.2.1
  have hq' := q.2.2
  have hexp : Real.exp t ≤ 1 + t + t ^ 2 := by
    have h := Real.norm_exp_sub_one_sub_id_le (by simpa [Real.norm_eq_abs] using ht)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs] at h
    linarith [le_trans (le_abs_self _) h]
  have h₁ : t * (1 - (q : ℝ)) - t ^ 2 * (q : ℝ) = t + (-((q : ℝ) * (t + t ^ 2))) := by
    ring
  have h₀ : t * (0 - (q : ℝ)) - t ^ 2 * (q : ℝ) = -((q : ℝ) * (t + t ^ 2)) := by
    ring
  rw [h₁, h₀, Real.exp_add]
  calc
    _ ≤ ((q : ℝ) * (1 + t + t ^ 2) + (1 - (q : ℝ))) *
          Real.exp (-((q : ℝ) * (t + t ^ 2))) := by
        rw [add_mul, ← mul_assoc]
        gcongr
    _ = ((q : ℝ) * (t + t ^ 2) + 1) * Real.exp (-((q : ℝ) * (t + t ^ 2))) := by ring
    _ ≤ Real.exp ((q : ℝ) * (t + t ^ 2)) * Real.exp (-((q : ℝ) * (t + t ^ 2))) :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
private def indicesBefore (n m : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.val < m

private theorem indicesBefore_succ {m : ℕ} (hm : m < n) :
    indicesBefore n (m + 1) = insert ⟨m, hm⟩ (indicesBefore n m) := by
  ext i
  simp only [indicesBefore, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Fin.ext_iff]
  omega

private def UsesPast (g : Fin n → Bits n → ℝ) : Prop :=
  ∀ i ω ω', (∀ j, j < i → ω j = ω' j) → g i ω = g i ω'

private noncomputable def score (q t u x : ℝ) : ℝ :=
  t * ((x - q) * u) - t ^ 2 * (q * u ^ 2)

private noncomputable def expSum (p : Fin n → I) (g : Fin n → Bits n → ℝ)
    (t : ℝ) (m : ℕ) (ω : Bits n) : ℝ :=
  Real.exp (∑ i ∈ indicesBefore n m, score (p i) t (g i ω) (bit ω i))

/-- The exponential with a quadratic compensator has mean at most one. -/
private theorem integral_expSum_le_one (p : Fin n → I) (g : Fin n → Bits n → ℝ)
    (hg : UsesPast g) (t : ℝ) (hsmall : ∀ i ω, |t * g i ω| ≤ 1) (m : ℕ) (hm : m ≤ n) :
    (∫ ω, expSum p g t m ω ∂(randomSubsetLaw p)) ≤ 1 := by
  induction m with
  | zero => simp [expSum, indicesBefore]
  | succ m ih =>
    have hmn : m < n := by omega
    let i : Fin n := ⟨m, hmn⟩
    have hi : i ∉ indicesBefore n m := by simp [i, indicesBefore]
    have hsplit (ω : Bits n) : expSum p g t (m + 1) ω =
        if ω i then expSum p g t m ω * Real.exp (score (p i) t (g i ω) 1)
        else expSum p g t m ω * Real.exp (score (p i) t (g i ω) 0) := by
      have hind := indicesBefore_succ hmn
      cases hω : ω i <;>
        simp [expSum, hind, ← show i = ⟨m, hmn⟩ from rfl, Finset.sum_insert hi,
          Real.exp_add, bit, hω, mul_comm]
    have hsame (x : ℝ) (ω ω' : Bits n) (h : ∀ j, j ≠ i → ω j = ω' j) :
        expSum p g t m ω * Real.exp (score (p i) t (g i ω) x) =
        expSum p g t m ω' * Real.exp (score (p i) t (g i ω') x) := by
      have hpast : ∀ j, j < i → ω j = ω' j := fun j hj => h j hj.ne
      rw [hg i ω ω' hpast]
      congr 1
      unfold expSum
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < i := (Finset.mem_filter.mp hj).2
      rw [hg j ω ω' (fun l hl => hpast l (hl.trans hj'))]
      simp only [bit, hpast j hj']
    simp_rw [hsplit]
    rw [integral_select p i _ _ (hsame 1) (hsame 0), ← integral_const_mul,
      ← integral_const_mul, ← integral_add Integrable.of_finite Integrable.of_finite]
    refine (integral_mono Integrable.of_finite Integrable.of_finite (fun ω => ?_)).trans
      (ih (by omega))
    have he (x : ℝ) : score (p i) t (g i ω) x =
        (t * g i ω) * (x - (p i : ℝ)) - (t * g i ω) ^ 2 * (p i : ℝ) := by
      unfold score
      ring
    dsimp only
    rw [he 1, he 0]
    calc
      _ = expSum p g t m ω * ((p i : ℝ) *
            Real.exp ((t * g i ω) * (1 - (p i : ℝ)) - (t * g i ω) ^ 2 * (p i : ℝ)) +
          (1 - (p i : ℝ)) *
            Real.exp ((t * g i ω) * (0 - (p i : ℝ)) - (t * g i ω) ^ 2 * (p i : ℝ))) := by
        ring
      _ ≤ expSum p g t m ω * 1 :=
        mul_le_mul_of_nonneg_left (bernoulli_exp (p i) (hsmall i ω))
          (Real.exp_pos _).le
      _ = _ := mul_one _

private noncomputable def incrementSum (p : Fin n → I) (g : Fin n → Bits n → ℝ)
    (ω : Bits n) : ℝ :=
  ∑ i, (bit ω i - (p i : ℝ)) * g i ω

private noncomputable def varianceBound (p : Fin n → I) (g : Fin n → Bits n → ℝ)
    (ω : Bits n) : ℝ :=
  ∑ i, (p i : ℝ) * (g i ω) ^ 2

private theorem expSum_full (p : Fin n → I) (g : Fin n → Bits n → ℝ) (t : ℝ) (ω : Bits n) :
    expSum p g t n ω =
      Real.exp (t * incrementSum p g ω - t ^ 2 * varianceBound p g ω) := by
  have h : indicesBefore n n = Finset.univ := by ext i; simp [indicesBefore]
  simp only [expSum, h, score, Finset.sum_sub_distrib, ← Finset.mul_sum, incrementSum,
    varianceBound]

/-- A two-sided tail estimate on outcomes with bounded coefficients and variance. -/
private theorem increment_tail (p : Fin n → I) (g : Fin n → Bits n → ℝ)
    (hg : UsesPast g) (hg0 : ∀ i ω, 0 ≤ g i ω) {B V t x lam : ℝ}
    (hB : 0 ≤ B) (ht : 0 ≤ t) (htB : t * B ≤ 1)
    (hcut : lam ≤ t * x - t ^ 2 * V) :
    (randomSubsetLaw p).real
      {ω | (∀ i, g i ω ≤ B) ∧ varianceBound p g ω ≤ V ∧ x < |incrementSum p g ω|} ≤
      2 * Real.exp (-lam) := by
  let clipped : Fin n → Bits n → ℝ := fun i ω => min B (g i ω)
  have hc : UsesPast clipped := by
    intro i ω ω' h
    exact congrArg (min B) (hg i ω ω' h)
  let exponent (s : ℝ) (ω : Bits n) :=
    s * incrementSum p clipped ω - s ^ 2 * varianceBound p clipped ω
  have htail (s : ℝ) (hs : |s| = t) :
      (randomSubsetLaw p).real {ω | lam ≤ exponent s ω} ≤ Real.exp (-lam) := by
    apply tail_of_exp
    have hsmall (i : Fin n) (ω : Bits n) : |s * clipped i ω| ≤ 1 := by
      rw [abs_mul, hs, abs_of_nonneg (le_min hB (hg0 i ω))]
      exact (mul_le_mul_of_nonneg_left (min_le_left _ _) ht).trans htB
    simpa only [expSum_full] using integral_expSum_le_one p clipped hc s hsmall n le_rfl
  rw [two_mul]
  refine (measureReal_mono (s₂ := {ω | lam ≤ exponent t ω} ∪
    {ω | lam ≤ exponent (-t) ω}) ?_).trans
    ((measureReal_union_le _ _).trans (add_le_add
      (htail t (abs_of_nonneg ht)) (htail (-t) (by rw [abs_neg, abs_of_nonneg ht]))))
  rintro ω ⟨hω, hv, hx⟩
  have hclip : ∀ i, clipped i ω = g i ω := fun i => min_eq_right (hω i)
  have hi : incrementSum p clipped ω = incrementSum p g ω := by
    simp only [incrementSum, hclip]
  have hv' : varianceBound p clipped ω = varianceBound p g ω := by
    simp only [varianceBound, hclip]
  rcases lt_abs.mp hx with hpos | hneg
  · left
    change lam ≤ t * incrementSum p clipped ω - t ^ 2 * varianceBound p clipped ω
    rw [hi, hv']
    exact hcut.trans (sub_le_sub (mul_le_mul_of_nonneg_left hpos.le ht)
      (mul_le_mul_of_nonneg_left hv (sq_nonneg t)))
  · right
    change lam ≤ -t * incrementSum p clipped ω - (-t) ^ 2 * varianceBound p clipped ω
    rw [hi, hv', neg_sq, neg_mul, ← mul_neg]
    exact hcut.trans (sub_le_sub (mul_le_mul_of_nonneg_left (by linarith) ht)
      (mul_le_mul_of_nonneg_left hv (sq_nonneg t)))
private def before (i : Fin n) (e : Finset (Fin n)) : Finset (Fin n) :=
  e.filter (· < i)

private def after (i : Fin n) (e : Finset (Fin n)) : Finset (Fin n) :=
  e.filter (i < ·)

private theorem disjoint_before_after (i : Fin n) (e : Finset (Fin n)) :
    Disjoint (before i e) (after i e) := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  exact ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hj').2).false

private theorem before_union_after_sdiff (i : Fin n) (e A : Finset (Fin n))
    (hA : A ⊆ before i e) :
    (before i e \ A) ∪ after i e = e \ insert i A := by
  ext j
  simp only [before, after, Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_insert, not_or]
  have hlt : j ∈ A → j < i := fun h => (Finset.mem_filter.mp (hA h)).2
  rcases lt_trichotomy j i with h | rfl | h
  · have h' : ¬i < j := not_lt_of_ge h.le
    simp [h, h.ne, h']
  · simp
  · have h' : ¬j < i := not_lt_of_ge h.le
    have hjA : j ∉ A := fun hj => h' (hlt hj)
    simp [h, h.ne', h', hjA]

private noncomputable def gainWeight (p : Fin n → I) (i : Fin n)
    (e : Finset (Fin n)) (x : ℝ) : ℝ :=
  x * ∏ j ∈ after i e, (p j : ℝ)

private theorem gainWeight_nonneg (p : Fin n → I) (i : Fin n) (e : Finset (Fin n))
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gainWeight p i e x :=
  mul_nonneg hx (Finset.prod_nonneg fun j _ => (p j).2.1)

private theorem gainWeight_effectTerm (p : Fin n → I) (i : Fin n)
    (e A : Finset (Fin n)) (x : ℝ) (hi : i ∈ e) (hA : A ⊆ before i e) :
    effectTerm p (before i e) A (gainWeight p i e x) = effectTerm p e (insert i A) x := by
  have hAe : A ⊆ e := hA.trans (Finset.filter_subset _ _)
  have hdisj : Disjoint (before i e \ A) (after i e) :=
    (disjoint_before_after i e).mono_left Finset.sdiff_subset
  rw [effectTerm, ite_eq_left hA, effectTerm, ite_eq_left (Finset.insert_subset hi hAe),
    ← before_union_after_sdiff i e A hA, Finset.prod_union hdisj, gainWeight]
  ring

private theorem reweighted_effectTerm_le (p : Fin n → I) (i : Fin n)
    (e A : Finset (Fin n)) {x : ℝ} (hx : 0 ≤ x) (hi : i ∈ e) :
    effectTerm p (before i e) A ((p i : ℝ) * gainWeight p i e x) ≤ effectTerm p e A x := by
  by_cases hA : A ⊆ before i e
  · have hAe : A ⊆ e := hA.trans (Finset.filter_subset _ _)
    have hiA : i ∉ A := fun h => (lt_irrefl i) (Finset.mem_filter.mp (hA h)).2
    have hprod : (p i : ℝ) * (∏ j ∈ e \ insert i A, (p j : ℝ)) =
        ∏ j ∈ e \ A, (p j : ℝ) := by
      rw [Finset.sdiff_insert]
      exact Finset.mul_prod_erase (e \ A) (fun j => (p j : ℝ)) (Finset.mem_sdiff.mpr ⟨hi, hiA⟩)
    have hmul :
        effectTerm p (before i e) A ((p i : ℝ) * gainWeight p i e x) =
          (p i : ℝ) * effectTerm p (before i e) A (gainWeight p i e x) := by
      simp only [effectTerm, hA, ite_true, mul_assoc]
    rw [hmul, gainWeight_effectTerm p i e A x hi hA, effectTerm, effectTerm,
      ite_eq_left (Finset.insert_subset hi hAe), ite_eq_left hAe, mul_left_comm, hprod]
  · simpa only [effectTerm, hA, ite_false] using effectTerm_nonneg p e A hx

private noncomputable def gain {ι : Type} (p : Fin n → I) (S : Finset ι)
    (edge : ι → Finset (Fin n)) (w : ι → ℝ) (i : Fin n) (ω : Bits n) : ℝ :=
  poly (S.filter fun a => i ∈ edge a) (fun a => before i (edge a))
    (fun a => gainWeight p i (edge a) (w a)) ω

private theorem gain_nonneg {ι : Type} (p : Fin n → I) (S : Finset ι)
    (edge : ι → Finset (Fin n)) (w : ι → ℝ) (hw : ∀ a ∈ S, 0 ≤ w a) (i : Fin n)
    (ω : Bits n) : 0 ≤ gain p S edge w i ω := by
  exact Finset.sum_nonneg fun a ha =>
    mul_nonneg (gainWeight_nonneg _ _ _ (hw a (Finset.mem_filter.mp ha).1))
      (Finset.prod_nonneg fun j _ => bit_nonneg ω j)

private theorem gain_usesPast {ι : Type} (p : Fin n → I) (S : Finset ι)
    (edge : ι → Finset (Fin n)) (w : ι → ℝ) : UsesPast (gain p S edge w) := by
  intro i ω ω' hagree
  refine Finset.sum_congr rfl fun a _ => congrArg (gainWeight p i (edge a) (w a) * ·) ?_
  exact Finset.prod_congr rfl fun j hj => by rw [bit, bit, hagree j (Finset.mem_filter.mp hj).2]

private theorem gain_degree {k : ℕ} {ι : Type} (S : Finset ι)
    (edge : ι → Finset (Fin n)) (hdeg : ∀ a ∈ S, (edge a).card ≤ k + 1)
    (i : Fin n) (a : ι) (ha : a ∈ S) (hi : i ∈ edge a) :
    (before i (edge a)).card ≤ k := by
  have hsub : before i (edge a) ⊆ (edge a).erase i := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hj).2.ne, (Finset.mem_filter.mp hj).1⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hi] at hle
  exact hle.trans (Nat.sub_le_sub_right (hdeg a ha) 1)

private theorem gain_effect_le {ι : Type} (p : Fin n → I) (S : Finset ι)
    (edge : ι → Finset (Fin n)) (w : ι → ℝ) (hw : ∀ a ∈ S, 0 ≤ w a)
    (i : Fin n) (A : Finset (Fin n)) :
    effect p (S.filter fun a => i ∈ edge a) (fun a => before i (edge a))
      (fun a => gainWeight p i (edge a) (w a)) A ≤ effect p S edge w (insert i A) := by
  unfold effect
  refine le_trans (Finset.sum_le_sum (g := fun a => effectTerm p (edge a) (insert i A) (w a)) ?_) ?_
  · intro a ha
    have ⟨has, hi⟩ := Finset.mem_filter.mp ha
    by_cases hA : A ⊆ before i (edge a)
    · exact (gainWeight_effectTerm p i _ A _ hi hA).le
    · simpa only [effectTerm, hA, ite_false] using effectTerm_nonneg p (edge a) _ (hw a has)
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun a ha _ =>
      effectTerm_nonneg p _ _ (hw a ha)

private noncomputable def weightedGainSum {ι : Type} (p : Fin n → I) (S : Finset ι)
    (edge : ι → Finset (Fin n)) (w : ι → ℝ) (ω : Bits n) : ℝ :=
  poly (S.sigma edge) (fun a => before a.2 (edge a.1))
    (fun a => (p a.2 : ℝ) * gainWeight p a.2 (edge a.1) (w a.1)) ω

private theorem weightedGainSum_eq_sum {ι : Type} (p : Fin n → I) (S : Finset ι)
    (edge : ι → Finset (Fin n)) (w : ι → ℝ) (ω : Bits n) :
    weightedGainSum p S edge w ω = ∑ i, (p i : ℝ) * gain p S edge w i ω := by
  classical
  simp only [weightedGainSum, gain, poly, Finset.sum_sigma, Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [mul_assoc, mul_ite, mul_zero, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.univ_inter]

private theorem weightedGainSum_effect_le {k : ℕ} {ι : Type} (p : Fin n → I) (S : Finset ι)
    (edge : ι → Finset (Fin n)) (w : ι → ℝ) (hw : ∀ a ∈ S, 0 ≤ w a)
    (hdeg : ∀ a ∈ S, (edge a).card ≤ k + 1) (A : Finset (Fin n)) :
    effect p (S.sigma edge) (fun a => before a.2 (edge a.1))
      (fun a => (p a.2 : ℝ) * gainWeight p a.2 (edge a.1) (w a.1)) A ≤
      (↑k + 1) * effect p S edge w A := by
  rw [effect, Finset.sum_sigma, effect, Finset.mul_sum]
  refine Finset.sum_le_sum fun a ha => ?_
  calc
    _ ≤ ∑ _i ∈ edge a, effectTerm p (edge a) A (w a) := Finset.sum_le_sum fun i hi =>
      reweighted_effectTerm_le p i _ A (hw a ha) hi
    _ = ((edge a).card : ℝ) * effectTerm p (edge a) A (w a) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg a ha)
      (effectTerm_nonneg p _ _ (hw a ha))

private theorem varianceBound_gain_le {ι : Type} (p : Fin n → I) (S : Finset ι)
    (edge : ι → Finset (Fin n)) (w : ι → ℝ) (hw : ∀ a ∈ S, 0 ≤ w a) (ω : Bits n) (B : ℝ)
    (hB : ∀ i, gain p S edge w i ω ≤ B) :
    varianceBound p (gain p S edge w) ω ≤ B * weightedGainSum p S edge w ω := by
  rw [varianceBound, weightedGainSum_eq_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [pow_two, mul_left_comm B]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hB i)
    (gain_nonneg p S edge w hw i ω)) (p i).2.1
private noncomputable def mixedBit (p : Fin n → I) (m : ℕ) (ω : Bits n) (j : Fin n) : ℝ :=
  if j.val < m then bit ω j else (p j : ℝ)

private noncomputable def revealed {ι : Type} (p : Fin n → I) (S : Finset ι)
    (edge : ι → Finset (Fin n)) (w : ι → ℝ) (m : ℕ) (ω : Bits n) : ℝ :=
  ∑ a ∈ S, w a * ∏ j ∈ edge a, mixedBit p m ω j

private theorem prod_mixedBit_erase (p : Fin n → I) (i : Fin n) (e : Finset (Fin n))
    (ω : Bits n) :
    (∏ j ∈ e.erase i, mixedBit p i.val ω j) =
      (∏ j ∈ before i e, bit ω j) * ∏ j ∈ after i e, (p j : ℝ) := by
  have he : before i e ∪ after i e = e.erase i := by
    simpa [Finset.sdiff_singleton_eq_erase] using
      before_union_after_sdiff i e ∅ (Finset.empty_subset _)
  rw [← he, Finset.prod_union (disjoint_before_after i e)]
  congr 1
  · exact Finset.prod_congr rfl fun j hj =>
      ite_eq_left (Finset.mem_filter.mp hj).2
  · exact Finset.prod_congr rfl fun j hj =>
      ite_eq_right (not_lt_of_ge (Finset.mem_filter.mp hj).2.le)

private theorem revealed_step {ι : Type} (p : Fin n → I) (S : Finset ι)
    (edge : ι → Finset (Fin n)) (w : ι → ℝ) (i : Fin n) (ω : Bits n) :
    revealed p S edge w (i.val + 1) ω - revealed p S edge w i.val ω =
      (bit ω i - (p i : ℝ)) * gain p S edge w i ω := by
  simp only [revealed, gain, poly, Finset.mul_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsame (j : Fin n) (hj : j ≠ i) :
      mixedBit p (i.val + 1) ω j = mixedBit p i.val ω j := by
    have hv : j.val ≠ i.val := fun h => hj (Fin.ext h)
    have hle : j.val < i.val + 1 ↔ j.val < i.val := by omega
    simp [mixedBit, hle]
  by_cases hi : i ∈ edge a
  · have hprod :
        (∏ j ∈ (edge a).erase i, mixedBit p (i.val + 1) ω j) =
          ∏ j ∈ (edge a).erase i, mixedBit p i.val ω j :=
      Finset.prod_congr rfl fun j hj => hsame j (Finset.mem_erase.mp hj).1
    rw [ite_eq_left hi, ← Finset.mul_prod_erase _ (mixedBit p (i.val + 1) ω) hi,
      ← Finset.mul_prod_erase _ (mixedBit p i.val ω) hi, hprod,
      prod_mixedBit_erase p i (edge a) ω]
    simp only [mixedBit, Nat.lt_succ_self, lt_irrefl, ite_true, ite_false, gainWeight]
    ring
  · rw [ite_eq_right hi]
    rw [Finset.prod_congr rfl (g := mixedBit p i.val ω)
      (fun j hj => hsame j (fun h => hi (h ▸ hj))), sub_self, mul_zero]

private theorem incrementSum_gain {ι : Type} (p : Fin n → I) (S : Finset ι)
    (edge : ι → Finset (Fin n)) (w : ι → ℝ) (ω : Bits n) :
    incrementSum p (gain p S edge w) ω = poly S edge w ω - effect p S edge w ∅ := by
  have ht (m : ℕ) (hm : m ≤ n) :
      (∑ i ∈ indicesBefore n m, (bit ω i - (p i : ℝ)) * gain p S edge w i ω) =
        revealed p S edge w m ω - revealed p S edge w 0 ω := by
    induction m with
    | zero => simp [indicesBefore]
    | succ m ih =>
      have hmn : m < n := by omega
      let i : Fin n := ⟨m, hmn⟩
      have hi : i ∉ indicesBefore n m := by simp [i, indicesBefore]
      rw [indicesBefore_succ hmn, Finset.sum_insert hi, ih (by omega)]
      change _ * gain p S edge w i ω + _ = _
      rw [← revealed_step]
      change revealed p S edge w (m + 1) ω - revealed p S edge w m ω +
        (revealed p S edge w m ω - revealed p S edge w 0 ω) = _
      abel
  have hn : indicesBefore n n = Finset.univ := by ext i; simp [indicesBefore]
  simpa [hn, incrementSum, revealed, mixedBit, poly, effect, effectTerm] using ht n le_rfl
private noncomputable def scale (k : ℕ) (lam : ℝ) : ℝ :=
  (8 : ℝ) ^ k * Real.sqrt (k.factorial : ℝ) * lam ^ k

private theorem one_le_scale (k : ℕ) {lam : ℝ} (hlam : 1 ≤ lam) : 1 ≤ scale k lam := by
  have hfact : (1 : ℝ) ≤ k.factorial := by
    exact_mod_cast Nat.factorial_pos k
  unfold scale
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num))
      (by simpa using Real.sqrt_le_sqrt hfact)) (one_le_pow₀ hlam)

private theorem scale_succ (k : ℕ) (lam : ℝ) :
    scale (k + 1) lam = 8 * Real.sqrt ((k : ℝ) + 1) * scale k lam * lam := by
  simp only [scale, pow_succ _ k, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  rw [Real.sqrt_mul (by positivity)]
  ring

private def tailConstant : ℕ → ℝ
  | 0 => 0
  | k + 1 => 2 + 2 * tailConstant k

private theorem tailConstant_nonneg (k : ℕ) : 0 ≤ tailConstant k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change 0 ≤ 2 + 2 * tailConstant k
    linarith

private theorem sqrt_mul_le_left {r s : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    Real.sqrt (r * s) ≤ r := by
  calc
    Real.sqrt (r * s) ≤ Real.sqrt (r * r) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsr (hs.trans hsr))
    _ = r := by rw [← sq, Real.sqrt_sq (hs.trans hsr)]

private theorem count_bad_events {n : ℕ} (hn : 0 < n) (k : ℕ) (lam : ℝ) :
    (n : ℝ) * (tailConstant k * Real.exp (-lam) * (n : ℝ) ^ (k - 1)) +
        tailConstant k * Real.exp (-lam) * (n : ℝ) ^ (k - 1) + 2 * Real.exp (-lam) ≤
      tailConstant (k + 1) * Real.exp (-lam) * (n : ℝ) ^ k := by
  cases k with
  | zero => simp [tailConstant]
  | succ j =>
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hmono : (n : ℝ) ^ j ≤ (n : ℝ) ^ (j + 1) :=
      pow_le_pow_right₀ hn' (Nat.le_succ _)
    have hh : 2 * Real.exp (-lam) ≤ 2 * Real.exp (-lam) * (n : ℝ) ^ (j + 1) :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hn')
    simp only [Nat.succ_sub_one]
    change _ ≤ (2 + 2 * tailConstant (j + 1)) * Real.exp (-lam) * (n : ℝ) ^ (j + 1)
    have hmul : tailConstant (j + 1) * Real.exp (-lam) * (n : ℝ) ^ j ≤
        tailConstant (j + 1) * Real.exp (-lam) * (n : ℝ) ^ (j + 1) :=
      mul_le_mul_of_nonneg_left hmono (mul_nonneg (tailConstant_nonneg _) (Real.exp_pos _).le)
    rw [show (n : ℝ) * (tailConstant (j + 1) * Real.exp (-lam) * (n : ℝ) ^ j) =
      tailConstant (j + 1) * Real.exp (-lam) * (n : ℝ) ^ (j + 1) by rw [pow_succ]; ring]
    linarith

/-- Induct on the degree, using lower-degree polynomials for the predictable coefficients
and for their sum weighted by the Bernoulli means. -/
private theorem poly_tail (n : ℕ) (hn : 0 < n) (p : Fin n → I) (lam : ℝ) (hlam : 1 < lam)
    (k : ℕ) {ι : Type} (S : Finset ι) (edge : ι → Finset (Fin n)) (w : ι → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) (hdeg : ∀ a ∈ S, (edge a).card ≤ k)
    (r s : ℝ) (hs : 0 < s) (hsr : s ≤ r)
    (hmean : effect p S edge w ∅ ≤ r)
    (heffect : ∀ A : Finset (Fin n), A.Nonempty → effect p S edge w A ≤ s) :
    (randomSubsetLaw p).real
        {ω | scale k lam * Real.sqrt (r * s) < |poly S edge w ω - effect p S edge w ∅|} ≤
      tailConstant k * Real.exp (-lam) * (n : ℝ) ^ (k - 1) := by
  induction k generalizing ι S edge w r s with
  | zero =>
    have hz (a : ι) (ha : a ∈ S) : edge a = ∅ :=
      Finset.card_eq_zero.mp (Nat.le_zero.mp (hdeg a ha))
    have hconst (ω : Bits n) : poly S edge w ω = effect p S edge w ∅ := by
      unfold poly effect
      exact Finset.sum_congr rfl fun a ha => by simp [hz a ha, effectTerm]
    have hnonneg : 0 ≤ scale 0 lam * Real.sqrt (r * s) :=
      mul_nonneg ((zero_le_one : (0 : ℝ) ≤ 1).trans (one_le_scale _ hlam.le))
        (Real.sqrt_nonneg _)
    simp [hconst, not_lt_of_ge hnonneg, tailConstant]
  | succ k ih =>
    let D := scale k lam
    have hD : 1 ≤ D := one_le_scale _ hlam.le
    have hD0 : 0 < D := zero_lt_one.trans_le hD
    let q : ℝ := (k : ℝ) + 1
    have hq : 1 ≤ q := le_add_of_nonneg_left (Nat.cast_nonneg k)
    have hq0 : 0 < q := zero_lt_one.trans_le hq
    have hr : 0 < r := hs.trans_le hsr
    let error := tailConstant k * Real.exp (-lam) * (n : ℝ) ^ (k - 1)
    have upper {ι' : Type} (S' : Finset ι') (edge' : ι' → Finset (Fin n)) (w' : ι' → ℝ)
        (hw' : ∀ a ∈ S', 0 ≤ w' a) (hdeg' : ∀ a ∈ S', (edge' a).card ≤ k)
        (r' s' : ℝ) (hs' : 0 < s') (hsr' : s' ≤ r')
        (hmean' : effect p S' edge' w' ∅ ≤ r')
        (heffect' : ∀ A : Finset (Fin n), A.Nonempty → effect p S' edge' w' A ≤ s') :
        (randomSubsetLaw p).real {ω | 2 * D * r' < poly S' edge' w' ω} ≤ error := by
      refine (measureReal_mono (s₂ := {ω |
        D * Real.sqrt (r' * s') < |poly S' edge' w' ω - effect p S' edge' w' ∅|}) ?_).trans
        (ih S' edge' w' hw' hdeg' r' s' hs' hsr' hmean' heffect')
      intro ω hω
      change 2 * D * r' < poly S' edge' w' ω at hω
      have h₁ := mul_le_mul_of_nonneg_left (sqrt_mul_le_left hs'.le hsr') hD0.le
      have h₂ : r' ≤ D * r' := le_mul_of_one_le_left (hs'.le.trans hsr') hD
      exact (show D * Real.sqrt (r' * s') < poly S' edge' w' ω -
        effect p S' edge' w' ∅ by linarith).trans_le (le_abs_self _)
    let B := 2 * D * s
    let H := 2 * D * (q * r)
    have hgain (i : Fin n) :
        (randomSubsetLaw p).real {ω | B < gain p S edge w i ω} ≤ error := by
      refine upper _ _ _ ?_ ?_ s s hs le_rfl ?_ ?_
      · intro a ha
        exact gainWeight_nonneg _ _ _ (hw a (Finset.mem_filter.mp ha).1)
      · intro a ha
        exact gain_degree S edge hdeg i a (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp ha).2
      · exact (gain_effect_le p S edge w hw i ∅).trans
          (heffect _ ⟨i, Finset.mem_insert_self _ _⟩)
      · intro A _
        exact (gain_effect_le p S edge w hw i A).trans
          (heffect _ ⟨i, Finset.mem_insert_self _ _⟩)
    have hweightedSum :
        (randomSubsetLaw p).real {ω | H < weightedGainSum p S edge w ω} ≤ error := by
      refine upper _ _ _ ?_ ?_ (q * r) (q * s) (mul_pos hq0 hs)
        (mul_le_mul_of_nonneg_left hsr hq0.le) ?_ ?_
      · intro a ha
        exact mul_nonneg (p a.2).2.1
          (gainWeight_nonneg _ _ _ (hw a.1 (Finset.mem_sigma.mp ha).1))
      · intro a ha
        exact gain_degree S edge hdeg a.2 a.1 (Finset.mem_sigma.mp ha).1 (Finset.mem_sigma.mp ha).2
      · exact (weightedGainSum_effect_le p S edge w hw hdeg _).trans
          (mul_le_mul_of_nonneg_left hmean hq0.le)
      · intro A hA
        exact (weightedGainSum_effect_le p S edge w hw hdeg A).trans
          (mul_le_mul_of_nonneg_left (heffect A hA) hq0.le)
    let L := 2 * D * Real.sqrt q * Real.sqrt (r * s)
    have hL : 0 < L := by
      unfold L
      exact mul_pos (mul_pos (mul_pos (by norm_num) hD0) (Real.sqrt_pos.2 hq0))
        (Real.sqrt_pos.2 (mul_pos hr hs))
    have hBL : B ≤ L := by
      have hsqrt : s ≤ Real.sqrt (r * s) := by
        calc
          s = Real.sqrt (s ^ 2) := (Real.sqrt_sq hs.le).symm
          _ ≤ Real.sqrt (r * s) :=
            Real.sqrt_le_sqrt (by rw [sq]; exact mul_le_mul_of_nonneg_right hsr hs.le)
      have hqsqrt : 1 ≤ Real.sqrt q := by simpa using Real.sqrt_le_sqrt hq
      exact (mul_le_mul_of_nonneg_left hsqrt (by unfold D; positivity)).trans
        (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hqsqrt)
          (Real.sqrt_nonneg _))
    have hBH : B * H = L ^ 2 := by
      simp only [B, H, L, mul_pow, Real.sq_sqrt hq0.le, Real.sq_sqrt (mul_nonneg hr.le hs.le)]
      ring
    let x := scale (k + 1) lam * Real.sqrt (r * s)
    have hx : x = 4 * lam * L := by
      dsimp [x, L, D, q]
      rw [scale_succ]
      ring
    have ht : L⁻¹ * B ≤ 1 := by
      calc
        _ ≤ L⁻¹ * L := mul_le_mul_of_nonneg_left hBL (inv_nonneg.mpr hL.le)
        _ = 1 := inv_mul_cancel₀ hL.ne'
    have hcut : lam ≤ L⁻¹ * x - (L⁻¹) ^ 2 * L ^ 2 := by
      rw [hx, show L⁻¹ * (4 * lam * L) = 4 * lam * (L⁻¹ * L) by ring, ← mul_pow,
        inv_mul_cancel₀ hL.ne', mul_one, one_pow]
      linarith
    let badGain : Set (Bits n) := ⋃ i, {ω | B < gain p S edge w i ω}
    let badWeightedSum : Set (Bits n) := {ω | H < weightedGainSum p S edge w ω}
    let goodTail : Set (Bits n) := {ω | (∀ i, gain p S edge w i ω ≤ B) ∧
      varianceBound p (gain p S edge w) ω ≤ L ^ 2 ∧ x < |incrementSum p (gain p S edge w) ω|}
    have hbadGain : (randomSubsetLaw p).real badGain ≤ (n : ℝ) * error := by
      refine (measureReal_iUnion_fintype_le _).trans ?_
      simpa using (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hgain i)).trans_eq
        (show (∑ _i : Fin n, error) = (n : ℝ) * error by simp)
    have hgoodTail : (randomSubsetLaw p).real goodTail ≤ 2 * Real.exp (-lam) :=
      increment_tail p _ (gain_usesPast p S edge w) (gain_nonneg p S edge w hw)
        (by dsimp [B]; positivity) (inv_nonneg.mpr hL.le) ht hcut
    refine (measureReal_mono (s₂ := (badGain ∪ badWeightedSum) ∪ goodTail) ?_).trans ?_
    · intro ω hω
      by_cases hb : ω ∈ badGain ∪ badWeightedSum
      · exact Or.inl hb
      right
      have hgω (i : Fin n) : gain p S edge w i ω ≤ B := by
        apply le_of_not_gt
        exact fun hi => hb (Or.inl (Set.mem_iUnion.mpr ⟨i, hi⟩))
      have hhω : weightedGainSum p S edge w ω ≤ H := le_of_not_gt fun hh => hb (Or.inr hh)
      have hv : varianceBound p (gain p S edge w) ω ≤ L ^ 2 := by
        rw [← hBH]
        exact (varianceBound_gain_le p S edge w hw ω B hgω).trans
          (mul_le_mul_of_nonneg_left hhω (by dsimp [B]; positivity))
      exact ⟨hgω, hv, (incrementSum_gain p S edge w ω).symm ▸ hω⟩
    · calc
        _ ≤ (_ + _) + _ := (measureReal_union_le _ _).trans
          (add_le_add (measureReal_union_le _ _) le_rfl)
        _ ≤ ((n : ℝ) * error + error) + 2 * Real.exp (-lam) :=
          add_le_add (add_le_add hbadGain hweightedSum) hgoodTail
        _ ≤ _ := count_bad_events hn k lam
private theorem truncatedPoly_empty (E : Finset (Finset (Fin n))) (w : Finset (Fin n) → ℝ)
    (ω : Bits n) : truncatedPoly E w ∅ ω = poly E id w ω := by
  simp [truncatedPoly, poly, bit]

private theorem effect_le_maxAverageEffect (p : Fin n → I) (E : Finset (Finset (Fin n)))
    (w : Finset (Fin n) → ℝ) (A : Finset (Fin n)) :
    effect p E id w A ≤ maxAverageEffect p E w A.card := by
  rw [← integral_truncatedPoly, maxAverageEffect]
  let f (B : {B : Finset (Fin n) // B.card = A.card}) :=
    ∫ ω, truncatedPoly E w B.1 ω ∂(randomSubsetLaw p)
  exact le_ciSup (Set.finite_range f).bddAbove ⟨A, rfl⟩

private theorem measureReal_tail_eq_zero_of_empty_edges (p : Fin n → I)
    (E : Finset (Finset (Fin n))) (w : Finset (Fin n) → ℝ)
    (hE : ∀ e ∈ E, e = ∅) {x : ℝ} (hx : 0 ≤ x) :
    (randomSubsetLaw p).real
      {ω | x < |truncatedPoly E w ∅ ω - ∫ ω', truncatedPoly E w ∅ ω' ∂(randomSubsetLaw p)|} =
      0 := by
  have hconst (ω : Bits n) : truncatedPoly E w ∅ ω = ∑ e ∈ E, w e := by
    rw [truncatedPoly_empty]
    exact Finset.sum_congr rfl fun e he => by simp [hE e he]
  simp [hconst, not_lt_of_ge hx]

/-- **Kim–Vu concentration of positive polynomials (Main Theorem).** For every `k` there is a
constant `C > 0` such that the following holds. Let `t₁, …, tₙ` be independent `{0, 1}` random
variables with `E tᵢ = pᵢ`, let `Y = ∑_{e ∈ E} w(e) ∏_{i ∈ e} tᵢ` with positive weights and
edges of size at most `k`, and let `E_j` be the maximal average effect of `j` variables,
`E = max_{j ≥ 0} E_j` and `E' = max_{j ≥ 1} E_j`. Then for every `λ > 1`,
`P(|Y - E Y| > 8^k (k!)^{1/2} (E E')^{1/2} λ^k) ≤ C exp(-λ + (k - 1) log n)`.

(J. H. Kim and V. H. Vu, "Concentration of multivariate polynomials and its applications",
*Combinatorica* 20 (2000), 417–434, Section 1.2, Main Theorem, where the bound is written
`O(exp(-λ + (k - 1) log n))`. The theorem there also allows some `tᵢ` to be the constants
`pᵢ`; this entry states the case, singled out there, in which every `tᵢ` is a `{0, 1}`
variable. `E'` is the maximum over `1 ≤ j ≤ n`, which equals the maximum over all `j ≥ 1`
because `E_j = 0` for `j > n`.) -/
theorem kim_vu_concentration (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (p : Fin n → I) (E : Finset (Finset (Fin n)))
      (w : Finset (Fin n) → ℝ), (∀ e ∈ E, 0 < w e) → (∀ e ∈ E, e.card ≤ k) →
      ∀ lam : ℝ, 1 < lam →
        (randomSubsetLaw p).real
          {ω | (8 : ℝ) ^ k * Real.sqrt (k.factorial : ℝ) *
              Real.sqrt ((max (maxAverageEffect p E w 0)
                  (⨆ j : Fin n, maxAverageEffect p E w (j + 1))) *
                (⨆ j : Fin n, maxAverageEffect p E w (j + 1))) * lam ^ k <
            |truncatedPoly E w ∅ ω - ∫ ω', truncatedPoly E w ∅ ω' ∂(randomSubsetLaw p)|} ≤
          C * Real.exp (-lam + ((k : ℝ) - 1) * Real.log n) := by
  refine ⟨tailConstant k + 1, by linarith [tailConstant_nonneg k], ?_⟩
  intro n p E w hw hdeg lam hlam
  let s := ⨆ j : Fin n, maxAverageEffect p E w (j + 1)
  let r := max (maxAverageEffect p E w 0) s
  let x := (8 : ℝ) ^ k * Real.sqrt (k.factorial : ℝ) * Real.sqrt (r * s) * lam ^ k
  change (randomSubsetLaw p).real
    {ω | x < |truncatedPoly E w ∅ ω - ∫ ω', truncatedPoly E w ∅ ω' ∂(randomSubsetLaw p)|} ≤ _
  have hx0 : 0 ≤ x := by
    have hl : 0 < lam := zero_lt_one.trans hlam
    dsimp only [x]
    positivity
  have hRHS : 0 ≤ (tailConstant k + 1) * Real.exp (-lam + ((k : ℝ) - 1) * Real.log n) :=
    mul_nonneg (by linarith [tailConstant_nonneg k]) (Real.exp_pos _).le
  by_cases hk : k = 0
  · exact (measureReal_tail_eq_zero_of_empty_edges p E w (fun e he =>
      Finset.card_eq_zero.mp (Nat.le_zero.mp (hk ▸ hdeg e he))) hx0).le.trans hRHS
  by_cases hn : n = 0
  · have hE (e : Finset (Fin n)) : e = ∅ :=
      Finset.card_eq_zero.mp (Nat.le_zero.mp (by simpa [hn] using e.card_le_univ))
    exact (measureReal_tail_eq_zero_of_empty_edges p E w (fun e _ => hE e) hx0).le.trans hRHS
  have hw0 : ∀ e ∈ E, 0 ≤ w e := fun e he => (hw e he).le
  have heffect (A : Finset (Fin n)) (hA : A.Nonempty) : effect p E id w A ≤ s := by
    have hcard : A.card ≤ n := by simpa using A.card_le_univ
    have hcard0 := Finset.card_pos.mpr hA
    let j : Fin n := ⟨A.card - 1, by omega⟩
    have hj : j.val + 1 = A.card := by dsimp [j]; omega
    exact (effect_le_maxAverageEffect p E w A).trans
      (hj ▸ le_ciSup (Set.finite_range fun j : Fin n =>
        maxAverageEffect p E w (j + 1)).bddAbove j)
  by_cases hs : 0 < s
  swap
  · have hE (e : Finset (Fin n)) (he : e ∈ E) : e = ∅ := by
      by_contra! he0
      have hterm : w e ≤ effect p E id w e := by
        unfold effect
        refine le_trans ?_ (Finset.single_le_sum
          (fun a ha => effectTerm_nonneg p (id a) e (hw0 a ha)) he)
        simp [effectTerm]
      exact hs ((hw e he).trans_le (hterm.trans (heffect e he0)))
    exact (measureReal_tail_eq_zero_of_empty_edges p E w hE hx0).le.trans hRHS
  have hmean : effect p E id w ∅ ≤ r :=
    (effect_le_maxAverageEffect p E w ∅).trans (le_max_left _ _)
  have hcore := poly_tail n (Nat.pos_of_ne_zero hn) p lam hlam k E id w hw0 hdeg
    r s hs (le_max_right _ _) hmean heffect
  have hx : x = scale k lam * Real.sqrt (r * s) := by
    unfold x scale
    ring
  have hpow : Real.exp (-lam + ((k : ℝ) - 1) * Real.log n) =
      Real.exp (-lam) * (n : ℝ) ^ (k - 1) := by
    have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      simpa only [Nat.cast_one] using
        (Nat.cast_sub (R := ℝ) (Nat.pos_of_ne_zero hk))
    rw [Real.exp_add, ← hcast, Real.exp_nat_mul,
      Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hn)]
  simp_rw [hx, truncatedPoly_empty, integral_poly]
  refine hcore.trans ?_
  rw [hpow, mul_assoc]
  exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) (by positivity)

end MathlibExt.Probability.KimVuConcentrationWanted
