/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Integration

/-!
# The Alon–Matias–Szegedy sketch for the second frequency moment

For a stream `a₁, …, a_m` of elements of a finite set `ι`, let `mᵢ` be the number of occurrences
of `i` and `F₂ = ∑ᵢ mᵢ²` the second frequency moment. Alon, Matias and Szegedy draw random signs
`εᵢ ∈ {-1, 1}` that are four-wise independent with mean zero, maintain the linear sketch
`Z = ∑ᵢ εᵢ mᵢ` in one pass (add `ε_a` for each arriving `a`), and output `X = Z²`. Then
`E[X] = F₂` and `Var X = 4 ∑_{i<j} mᵢ² mⱼ² ≤ 2 F₂²`
(N. Alon, Y. Matias and M. Szegedy, "The space complexity of approximating the frequency moments",
J. Comput. System Sci. 58 (1999) 137–147, proof of Theorem 2.2).

## Main results

- `FourWiseIndependent`: every subfamily of at most four signs is mutually independent.
- `sketch_eq_sum_count_mul`: the one-pass sketch equals `∑ᵢ mᵢ εᵢ`.
- `integral_sq_weightedSum`, `variance_sq_weightedSum`: unbiasedness and the exact variance for
  arbitrary real weights `mᵢ`.
- `integral_sketch_sq`, `variance_sketch_sq`, `variance_sketch_sq_le`: the same statements for
  the frequencies of a stream, in the source's form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace MathlibExt.Probability.Streaming.AMS

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Four-wise independent random variables.** A family `ε : ι → Ω → ℝ` is four-wise independent
under `μ` if every subfamily indexed by a finite set of at most four indices is mutually
independent (N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), proof of
Theorem 2.2, where the signs are drawn from an orthogonal array of strength 4). -/
def FourWiseIndependent (ε : ι → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ S : Finset ι, S.card ≤ 4 → iIndepFun (fun i : S => ε i) μ

/-- **Frequency of an element in a stream.** The number `mᵢ` of occurrences of `i` in the stream
`l`, as a real number. -/
def freq [DecidableEq ι] (l : List ι) (i : ι) : ℝ := (l.count i : ℝ)

/-- **Second frequency moment of a stream.** `F₂ = ∑ᵢ mᵢ²`, where `mᵢ` is the number of
occurrences of `i` in the stream `l` (N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci.
58 (1999), Section 1). -/
def secondMoment [Fintype ι] [DecidableEq ι] (l : List ι) : ℝ := ∑ i, freq l i ^ 2

/-- **The AMS sketch of a stream.** The value `Z = ∑_{t} ε_{a_t}` accumulated in one pass over the
stream `l = (a₁, …, a_m)`, adding the sign of each arriving element (N. Alon, Y. Matias and
M. Szegedy, J. Comput. System Sci. 58 (1999), proof of Theorem 2.2). -/
def sketch (ε : ι → Ω → ℝ) (l : List ι) (ω : Ω) : ℝ := (l.map fun a => ε a ω).sum

omit [MeasurableSpace Ω] in
/-- **The one-pass sketch is linear in the frequencies.** For every stream `l`,
`∑_{t} ε_{a_t} = ∑ᵢ mᵢ εᵢ`, so the sketch `Z = ∑ᵢ εᵢ mᵢ` of Alon, Matias and Szegedy can be
maintained with one addition per arriving element (J. Comput. System Sci. 58 (1999), proof of
Theorem 2.2: "Z is a linear function of the numbers mᵢ, and can thus be computed in one
pass"). -/
theorem sketch_eq_sum_count_mul [Fintype ι] [DecidableEq ι] (ε : ι → Ω → ℝ) (l : List ι)
    (ω : Ω) : sketch ε l ω = ∑ i, freq l i * ε i ω := by
  induction l with
  | nil => simp [sketch, freq]
  | cons a l ih =>
    have h1 : sketch ε (a :: l) ω = ε a ω + sketch ε l ω := by simp [sketch]
    rw [h1, ih]
    have h2 : ∀ i, freq (a :: l) i * ε i ω =
        (if i = a then ε i ω else 0) + freq l i * ε i ω := by
      intro i
      by_cases h : i = a
      · subst h; simp [freq, List.count_cons_self]; ring
      · simp [freq, Ne.symm h, h]
    simp_rw [h2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

section Moments

variable {ε : ι → Ω → ℝ}

omit [MeasurableSpace Ω] in
private theorem sq_eq_one (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (i : ι) (ω : Ω) :
    ε i ω ^ 2 = 1 := by
  rcases hsign i ω with h | h <;> rw [h] <;> norm_num

omit [MeasurableSpace Ω] in
private theorem abs_eq_one (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (i : ι) (ω : Ω) :
    |ε i ω| = 1 := by
  rcases hsign i ω with h | h <;> rw [h] <;> norm_num

omit [MeasurableSpace Ω] in
private theorem abs_le_one (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (i : ι) (ω : Ω) :
    |ε i ω| ≤ 1 := (abs_eq_one hsign i ω).le

/-- Bounded measurable functions are integrable for a probability measure. -/
private theorem integrable_of_bound [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (C : ℝ) (hC : ∀ ω, |f ω| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => by
    simpa [Real.norm_eq_abs] using hC ω)

private theorem integral_prod_eq_zero [IsProbabilityMeasure μ] (hmeas : ∀ i, Measurable (ε i))
    (hmean : ∀ i, μ[ε i] = 0) (hind : FourWiseIndependent ε μ) (S : Finset ι)
    (hS : S.Nonempty) (hcard : S.card ≤ 4) : ∫ ω, ∏ i ∈ S, ε i ω ∂μ = 0 := by
  have h := (hind S hcard).integral_fun_prod_eq_prod_integral
    (fun i => (hmeas i).aestronglyMeasurable)
  have h' : ∫ ω, ∏ i ∈ S, ε i ω ∂μ = ∏ i : S, μ[ε i] := by
    rw [← h]
    congr 1
    funext ω
    exact (Finset.prod_coe_sort S fun i => ε i ω).symm
  rw [h']
  obtain ⟨a, ha⟩ := hS
  exact Finset.prod_eq_zero (i := ⟨a, ha⟩) (Finset.mem_univ _) (hmean a)

private theorem integral_mul_two [IsProbabilityMeasure μ]
    (hmeas : ∀ i, Measurable (ε i))
    (hmean : ∀ i, μ[ε i] = 0) (hind : FourWiseIndependent ε μ) {a b : ι} (hab : a ≠ b) :
    ∫ ω, ε a ω * ε b ω ∂μ = 0 := by
  classical
  have := integral_prod_eq_zero hmeas hmean hind {a, b} (by simp) (by
    calc ({a, b} : Finset ι).card ≤ 2 := Finset.card_le_two
      _ ≤ 4 := by norm_num)
  simpa [Finset.prod_pair hab] using this

private theorem integral_mul_four [IsProbabilityMeasure μ]
    (hmeas : ∀ i, Measurable (ε i))
    (hmean : ∀ i, μ[ε i] = 0) (hind : FourWiseIndependent ε μ) {a b c d : ι}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ∫ ω, ε a ω * ε b ω * ε c ω * ε d ω ∂μ = 0 := by
  classical
  have hS : ({a, b, c, d} : Finset ι).card ≤ 4 := Finset.card_le_four
  have := integral_prod_eq_zero hmeas hmean hind {a, b, c, d} (by simp) hS
  have hp : ∀ ω, ∏ i ∈ ({a, b, c, d} : Finset ι), ε i ω = ε a ω * ε b ω * ε c ω * ε d ω := by
    intro ω
    rw [Finset.prod_insert (by simp [hab, hac, had]), Finset.prod_insert (by simp [hbc, hbd]),
      Finset.prod_pair hcd]
    ring
  simpa [hp] using this

/-- The fourth-order correlations of the signs: for `i ≠ j` and `k ≠ l`,
`E[εᵢ εⱼ ε_k ε_l]` is `1` when `{k, l} = {i, j}` and `0` otherwise. -/
private theorem integral_corr [IsProbabilityMeasure μ] [DecidableEq ι]
    (hmeas : ∀ i, Measurable (ε i))
    (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (hmean : ∀ i, μ[ε i] = 0)
    (hind : FourWiseIndependent ε μ) {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) :
    ∫ ω, ε i ω * ε j ω * (ε k ω * ε l ω) ∂μ =
      if (k = i ∧ l = j) ∨ (k = j ∧ l = i) then 1 else 0 := by
  have hsq := sq_eq_one hsign
  have two := fun {a b : ι} (h : a ≠ b) => integral_mul_two (μ := μ) hmeas hmean hind h
  by_cases h1 : k = i ∧ l = j
  · obtain ⟨rfl, rfl⟩ := h1
    simp only [and_self, true_or, ite_true]
    have : ∀ ω, ε k ω * ε l ω * (ε k ω * ε l ω) = 1 := fun ω => by
      linear_combination (ε l ω ^ 2) * hsq k ω + hsq l ω
    simp [this]
  by_cases h2 : k = j ∧ l = i
  · obtain ⟨rfl, rfl⟩ := h2
    simp only [and_self, or_true, ite_true]
    have : ∀ ω, ε l ω * ε k ω * (ε k ω * ε l ω) = 1 := fun ω => by
      linear_combination (ε l ω ^ 2) * hsq k ω + hsq l ω
    simp [this]
  have hc : ¬((k = i ∧ l = j) ∨ (k = j ∧ l = i)) := by tauto
  simp only [hc, ite_false]
  by_cases hki : k = i
  · subst hki
    have hlj : l ≠ j := fun h => h1 ⟨rfl, h⟩
    have : ∀ ω, ε k ω * ε j ω * (ε k ω * ε l ω) = ε j ω * ε l ω := fun ω => by
      linear_combination (ε j ω * ε l ω) * hsq k ω
    simp only [this]; exact two (Ne.symm hlj)
  by_cases hkj : k = j
  · subst hkj
    have hli : l ≠ i := fun h => h2 ⟨rfl, h⟩
    have : ∀ ω, ε i ω * ε k ω * (ε k ω * ε l ω) = ε i ω * ε l ω := fun ω => by
      linear_combination (ε i ω * ε l ω) * hsq k ω
    simp only [this]; exact two (Ne.symm hli)
  by_cases hli : l = i
  · subst hli
    have : ∀ ω, ε l ω * ε j ω * (ε k ω * ε l ω) = ε j ω * ε k ω := fun ω => by
      linear_combination (ε j ω * ε k ω) * hsq l ω
    simp only [this]; exact two (Ne.symm hkj)
  by_cases hlj : l = j
  · subst hlj
    have : ∀ ω, ε i ω * ε l ω * (ε k ω * ε l ω) = ε i ω * ε k ω := fun ω => by
      linear_combination (ε i ω * ε k ω) * hsq l ω
    simp only [this]; exact two (Ne.symm hki)
  have : ∀ ω, ε i ω * ε j ω * (ε k ω * ε l ω) = ε i ω * ε j ω * ε k ω * ε l ω := fun ω => by
    ring
  simp only [this]
  exact integral_mul_four hmeas hmean hind hij (Ne.symm hki) (Ne.symm hli) (Ne.symm hkj)
    (Ne.symm hlj) hkl

variable [Fintype ι] [DecidableEq ι]

/-- The off-diagonal part `W = ∑_{i ≠ j} mᵢ mⱼ εᵢ εⱼ` of `Z²`. -/
private noncomputable def offDiag (ε : ι → Ω → ℝ) (m : ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, ∑ j, if i ≠ j then m i * m j * (ε i ω * ε j ω) else 0

omit [MeasurableSpace Ω] in
private theorem sq_eq_add_offDiag (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (m : ι → ℝ)
    (ω : Ω) : (∑ i, m i * ε i ω) ^ 2 = ∑ i, m i ^ 2 + offDiag ε m ω := by
  rw [sq, Finset.sum_mul_sum, offDiag, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j, m i * ε i ω * (m j * ε j ω) = (if i = j then m i ^ 2 else 0) +
      (if i ≠ j then m i * m j * (ε i ω * ε j ω) else 0) := by
    intro j
    by_cases hij : i = j
    · subst hij
      simp only [ite_true, ne_eq, not_true_eq_false, ite_false, add_zero]
      linear_combination (m i ^ 2) * sq_eq_one hsign i ω
    · simp only [hij, ite_false, ne_eq, not_false_eq_true, ite_true, zero_add]
      ring
  simp_rw [h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

private theorem measurable_offDiag (hmeas : ∀ i, Measurable (ε i)) (m : ι → ℝ) :
    Measurable (offDiag ε m) := by
  unfold offDiag
  refine Finset.measurable_fun_sum _ fun i _ => Finset.measurable_fun_sum _ fun j _ => ?_
  split_ifs
  · exact measurable_const.mul ((hmeas i).mul (hmeas j))
  · exact measurable_const

omit [Fintype ι] [DecidableEq ι] in
private theorem integrable_corr [IsProbabilityMeasure μ] (hmeas : ∀ i, Measurable (ε i))
    (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (i j k l : ι) (c : ℝ) :
    Integrable (fun ω => c * (ε i ω * ε j ω * (ε k ω * ε l ω))) μ :=
  integrable_of_bound (measurable_const.mul (((hmeas i).mul (hmeas j)).mul
    ((hmeas k).mul (hmeas l)))) |c| fun ω => by simp [abs_mul, abs_eq_one hsign]

omit [Fintype ι] [DecidableEq ι] in
private theorem integrable_pair [IsProbabilityMeasure μ] (hmeas : ∀ i, Measurable (ε i))
    (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (i j : ι) (c : ℝ) :
    Integrable (fun ω => c * (ε i ω * ε j ω)) μ :=
  integrable_of_bound (measurable_const.mul ((hmeas i).mul (hmeas j))) |c| fun ω => by
    simp [abs_mul, abs_eq_one hsign]

omit [Fintype ι] in
private theorem integrable_offDiag_term [IsProbabilityMeasure μ]
    (hmeas : ∀ i, Measurable (ε i)) (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (m : ι → ℝ)
    (i j : ι) :
    Integrable (fun ω => if i ≠ j then m i * m j * (ε i ω * ε j ω) else 0) μ := by
  by_cases hij : i ≠ j
  · simpa only [hij, ne_eq, not_false_eq_true, ite_true] using
      integrable_pair hmeas hsign i j (m i * m j)
  · simpa only [hij, ite_false] using integrable_const (μ := μ) (0 : ℝ)

private theorem integrable_offDiag [IsProbabilityMeasure μ] (hmeas : ∀ i, Measurable (ε i))
    (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (m : ι → ℝ) : Integrable (offDiag ε m) μ := by
  have : offDiag ε m = fun ω => ∑ i, ∑ j,
      (if i ≠ j then m i * m j * (ε i ω * ε j ω) else 0) := rfl
  rw [this]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_offDiag_term hmeas hsign m i j

private theorem integral_offDiag [IsProbabilityMeasure μ] (hmeas : ∀ i, Measurable (ε i))
    (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (hmean : ∀ i, μ[ε i] = 0)
    (hind : FourWiseIndependent ε μ) (m : ι → ℝ) : ∫ ω, offDiag ε m ω ∂μ = 0 := by
  unfold offDiag
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_offDiag_term hmeas hsign m i j]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => integrable_offDiag_term hmeas hsign m i j]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hij : i ≠ j
  · simp only [hij, ne_eq, not_false_eq_true, ite_true]
    rw [integral_const_mul, integral_mul_two hmeas hmean hind hij, mul_zero]
  · simp only [hij, ite_false, integral_zero]

private theorem integral_offDiag_sq [IsProbabilityMeasure μ] (hmeas : ∀ i, Measurable (ε i))
    (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (hmean : ∀ i, μ[ε i] = 0)
    (hind : FourWiseIndependent ε μ) (m : ι → ℝ) :
    ∫ ω, offDiag ε m ω ^ 2 ∂μ = 2 * ∑ i, ∑ j ∈ univ.erase i, m i ^ 2 * m j ^ 2 := by
  set g : ι → ι → ι → ι → ℝ := fun i j k l =>
    if i ≠ j ∧ k ≠ l then m i * m j * m k * m l else 0 with hg
  -- Expand `W²` as a quadruple sum.
  have hexp : ∀ ω, offDiag ε m ω ^ 2 = ∑ i, ∑ j, ∑ k, ∑ l,
      g i j k l * (ε i ω * ε j ω * (ε k ω * ε l ω)) := by
    intro ω
    have h1 : offDiag ε m ω ^ 2 = ∑ i, ∑ k, ∑ j, ∑ l,
        (if i ≠ j then m i * m j * (ε i ω * ε j ω) else 0) *
          (if k ≠ l then m k * m l * (ε k ω * ε l ω) else 0) := by
      rw [offDiag, sq, Finset.sum_mul_sum]
      simp_rw [Finset.sum_mul_sum]
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => ?_
    by_cases hij : i ≠ j
    · by_cases hkl : k ≠ l
      · simp only [hg, hij, hkl, ne_eq, not_false_eq_true, and_self, ite_true]
        ring
      · simp only [hg, hkl, and_false, ite_false, mul_zero, zero_mul]
    · simp only [hg, hij, false_and, ite_false, zero_mul]
  simp_rw [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      integrable_corr hmeas hsign i j k l _]
  have hsum : ∀ i, ∫ ω, ∑ j, ∑ k, ∑ l, g i j k l * (ε i ω * ε j ω * (ε k ω * ε l ω)) ∂μ =
      ∑ j, ∑ k, ∑ l, g i j k l * ∫ ω, ε i ω * ε j ω * (ε k ω * ε l ω) ∂μ := by
    intro i
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
      integrable_finsetSum _ fun l _ => integrable_corr hmeas hsign i j k l _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      integrable_corr hmeas hsign i j k l _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => integrable_corr hmeas hsign i j k l _]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact integral_const_mul _ _
  simp_rw [hsum]
  -- The inner double sum over `(k, l)` for fixed `(i, j)`.
  have hinner : ∀ i j, ∑ k, ∑ l, g i j k l * ∫ ω, ε i ω * ε j ω * (ε k ω * ε l ω) ∂μ =
      if i ≠ j then 2 * (m i ^ 2 * m j ^ 2) else 0 := by
    intro i j
    by_cases hij : i ≠ j
    · simp only [hij, ne_eq, not_false_eq_true, ite_true]
      have hterm : ∀ k l, g i j k l * ∫ ω, ε i ω * ε j ω * (ε k ω * ε l ω) ∂μ =
          (if k = i then (if l = j then m i ^ 2 * m j ^ 2 else 0) else 0) +
            (if k = j then (if l = i then m i ^ 2 * m j ^ 2 else 0) else 0) := by
        intro k l
        by_cases hkl : k ≠ l
        · rw [integral_corr hmeas hsign hmean hind hij hkl]
          have hgv : g i j k l = m i * m j * m k * m l := by
            simp only [hg, hij, hkl, ne_eq, not_false_eq_true, and_self, ite_true]
          rw [hgv]
          clear hgv hexp hsum hg
          clear_value g
          by_cases hki : k = i <;> by_cases hlj : l = j <;> by_cases hkj : k = j <;>
            by_cases hli : l = i <;> simp_all <;> ring
        · have hgv : g i j k l = 0 := by
            simp [hg, hkl]
          rw [hgv, zero_mul]
          push Not at hkl
          subst hkl
          clear hgv hexp hsum hg
          clear_value g
          by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all
      simp_rw [hterm]
      simp [Finset.sum_add_distrib, Finset.sum_ite_irrel]
      ring
    · simp only [hij, ite_false]
      refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
      have hgv : g i j k l = 0 := by simp only [hg, hij, false_and, ite_false]
      rw [hgv, zero_mul]
  simp_rw [hinner]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter, Finset.filter_ne, Finset.mul_sum]

omit [DecidableEq ι] in
/-- **Unbiasedness of the AMS estimator.** Let `ε : ι → Ω → ℝ` be measurable `±1`-valued random
signs with mean zero that are four-wise independent, and let `mᵢ` be real weights. Then
`Z = ∑ᵢ mᵢ εᵢ` satisfies `E[Z²] = ∑ᵢ mᵢ²` (N. Alon, Y. Matias and M. Szegedy, J. Comput. System
Sci. 58 (1999), proof of Theorem 2.2; the source notes that pairwise independence suffices for
this step). -/
theorem integral_sq_weightedSum [IsProbabilityMeasure μ] (hmeas : ∀ i, Measurable (ε i))
    (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (hmean : ∀ i, μ[ε i] = 0)
    (hind : FourWiseIndependent ε μ) (m : ι → ℝ) :
    ∫ ω, (∑ i, m i * ε i ω) ^ 2 ∂μ = ∑ i, m i ^ 2 := by
  classical
  simp_rw [sq_eq_add_offDiag hsign m]
  have hW : Integrable (offDiag ε m) μ := integrable_offDiag hmeas hsign m
  rw [integral_add (integrable_const _) hW, integral_const, integral_offDiag hmeas hsign hmean
    hind m]
  simp

/-- **Variance of the AMS estimator.** Under the hypotheses of `integral_sq_weightedSum`, the
estimator `X = (∑ᵢ mᵢ εᵢ)²` has variance `Var X = 2 ∑_{i ≠ j} mᵢ² mⱼ²`, that is,
`4 ∑_{i<j} mᵢ² mⱼ²` as in N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999),
proof of Theorem 2.2. -/
theorem variance_sq_weightedSum [IsProbabilityMeasure μ] (hmeas : ∀ i, Measurable (ε i))
    (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (hmean : ∀ i, μ[ε i] = 0)
    (hind : FourWiseIndependent ε μ) (m : ι → ℝ) :
    variance (fun ω => (∑ i, m i * ε i ω) ^ 2) μ =
      2 * ∑ i, ∑ j ∈ univ.erase i, m i ^ 2 * m j ^ 2 := by
  have hZ : Measurable fun ω => (∑ i, m i * ε i ω) ^ 2 :=
    (Finset.measurable_fun_sum _ fun i _ => measurable_const.mul (hmeas i)).pow_const 2
  have hbound : ∀ ω, |(∑ i, m i * ε i ω) ^ 2| ≤ (∑ i, |m i|) ^ 2 := by
    intro ω
    rw [abs_pow]
    have : |∑ i, m i * ε i ω| ≤ ∑ i, |m i| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul]
      calc |m i| * |ε i ω| ≤ |m i| * 1 :=
            mul_le_mul_of_nonneg_left (abs_le_one hsign i ω) (abs_nonneg _)
        _ = |m i| := mul_one _
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have hL2 : MemLp (fun ω => (∑ i, m i * ε i ω) ^ 2) 2 μ :=
    MemLp.of_bound hZ.aestronglyMeasurable _ (Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using hbound ω)
  rw [variance_eq_integral hZ.aemeasurable]
  rw [integral_sq_weightedSum hmeas hsign hmean hind m]
  have : ∀ ω, ((∑ i, m i * ε i ω) ^ 2 - ∑ i, m i ^ 2) ^ 2 = offDiag ε m ω ^ 2 := by
    intro ω; rw [sq_eq_add_offDiag hsign m ω]; ring
  simp_rw [this]
  exact integral_offDiag_sq hmeas hsign hmean hind m

omit [DecidableEq ι] in
/-- **Variance bound for the AMS estimator.** Under the hypotheses of `integral_sq_weightedSum`,
`Var((∑ᵢ mᵢ εᵢ)²) ≤ 2 (∑ᵢ mᵢ²)²` (N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci. 58
(1999), proof of Theorem 2.2: `Var(X) ≤ 2 F₂²`). -/
theorem variance_sq_weightedSum_le [IsProbabilityMeasure μ] (hmeas : ∀ i, Measurable (ε i))
    (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (hmean : ∀ i, μ[ε i] = 0)
    (hind : FourWiseIndependent ε μ) (m : ι → ℝ) :
    variance (fun ω => (∑ i, m i * ε i ω) ^ 2) μ ≤ 2 * (∑ i, m i ^ 2) ^ 2 := by
  classical
  rw [variance_sq_weightedSum hmeas hsign hmean hind m, sq, Finset.sum_mul_sum]
  gcongr with i _
  exact Finset.erase_subset _ _

/-- **The AMS sketch is unbiased for `F₂`.** For measurable `±1`-valued, mean-zero, four-wise
independent signs `εᵢ` and every stream `l`, the one-pass sketch `Z = ∑_t ε_{a_t}` satisfies
`E[Z²] = F₂(l)` (N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), proof of
Theorem 2.2). -/
theorem integral_sketch_sq [IsProbabilityMeasure μ] (hmeas : ∀ i, Measurable (ε i))
    (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (hmean : ∀ i, μ[ε i] = 0)
    (hind : FourWiseIndependent ε μ) (l : List ι) :
    ∫ ω, sketch ε l ω ^ 2 ∂μ = secondMoment l := by
  simp_rw [sketch_eq_sum_count_mul]
  exact integral_sq_weightedSum hmeas hsign hmean hind _

/-- **Variance of the AMS sketch.** Under the hypotheses of `integral_sketch_sq`, the estimator
`X = Z²` of `F₂(l)` has variance `Var X = 2 ∑_{i ≠ j} mᵢ² mⱼ²`, which is the source's
`4 ∑_{i<j} mᵢ² mⱼ²` (N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), proof
of Theorem 2.2). -/
theorem variance_sketch_sq [IsProbabilityMeasure μ] (hmeas : ∀ i, Measurable (ε i))
    (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (hmean : ∀ i, μ[ε i] = 0)
    (hind : FourWiseIndependent ε μ) (l : List ι) :
    variance (fun ω => sketch ε l ω ^ 2) μ =
      2 * ∑ i, ∑ j ∈ univ.erase i, freq l i ^ 2 * freq l j ^ 2 := by
  simp_rw [sketch_eq_sum_count_mul]
  exact variance_sq_weightedSum hmeas hsign hmean hind _

/-- **Variance bound for the AMS sketch.** Under the hypotheses of `integral_sketch_sq`,
`Var(Z²) ≤ 2 F₂(l)²` (N. Alon, Y. Matias and M. Szegedy, J. Comput. System Sci. 58 (1999), proof
of Theorem 2.2), the bound that Chebyshev's inequality turns into a constant-probability
`(1 ± λ)`-approximation from the mean of `16 / λ²` independent copies. -/
theorem variance_sketch_sq_le [IsProbabilityMeasure μ] (hmeas : ∀ i, Measurable (ε i))
    (hsign : ∀ i ω, ε i ω = 1 ∨ ε i ω = -1) (hmean : ∀ i, μ[ε i] = 0)
    (hind : FourWiseIndependent ε μ) (l : List ι) :
    variance (fun ω => sketch ε l ω ^ 2) μ ≤ 2 * secondMoment l ^ 2 := by
  simp_rw [sketch_eq_sum_count_mul]
  exact variance_sq_weightedSum_le hmeas hsign hmean hind _

end Moments

end MathlibExt.Probability.Streaming.AMS
