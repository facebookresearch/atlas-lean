/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GeneralizationBounds.Stability
public import MathlibExt.Probability.Concentration.McDiarmidPi

/-!
# Uniform (remove-one) stability implies high-probability generalization

An algorithm is a family `A k : (Fin k → 𝒵) → H`, defined on every sample size, so that the
sample `S \ i` with its `i`-th point removed (`Fin.removeNth i S`, of size `n`) has an output. It
has remove-one uniform stability `β` at size `m = n + 1` with respect to a loss `L` if removing
any one point changes the loss at every test point by at most `β` (Olivier Bousquet and
André Elisseeff, *Stability and Generalization*, Journal of Machine Learning Research 2
(Mar 2002), pp. 499-526, Definition 6, p. 504). Then, for a loss with values in `[0, M]` on
samples of size `m`, with probability at least `1 - δ` over `S ~ ν^m`,
`R(A_S) ≤ R_emp(A_S) + 2β + (4mβ + M) √(ln(1/δ) / (2m))` (Theorem 12, inequality (11), p. 507).

The proof follows the source: remove-one stability `β` gives replace-one stability `2β`
(`isUniformlyStable_two_mul_of_isRemoveOneUniformlyStable`), so
`abs_integral_empiricalRisk_sub_risk_le` bounds `E[R - R_emp]` by `2β`; the function
`Φ(S) = R(A_S) - R_emp(A_S)` has bounded differences `4β + M/m`, and McDiarmid's inequality
(`ProbabilityTheory.measureReal_sub_integral_ge_le_of_bounded_differences`) gives the tail
display (pp. 507-508).

## Main definitions

- `IsRemoveOneUniformlyStable L A n β`: remove-one uniform stability `β` of the algorithm family
  `A` at sample size `n + 1`.

## Main results

- `abs_sub_le_two_mul_of_isRemoveOneUniformlyStable`: removing a point changes the loss by at
  most `β`, so replacing a point changes it by at most `2β`.
- `isUniformlyStable_two_mul_of_isRemoveOneUniformlyStable`: the same bound as replace-one
  uniform stability (`IsUniformlyStable`).
- `measureReal_lt_risk_sub_empiricalRisk_le_of_isRemoveOneUniformlyStable`: the tail bound
  (pp. 507-508) `P[R - R_emp > ε + 2β] ≤ exp(-2mε² / (4mβ + M)²)`.
- `one_sub_le_measureReal_risk_le_of_isRemoveOneUniformlyStable`: Theorem 12, inequality (11)
  (p. 507).
- `one_sub_le_measureReal_risk_le_of_isRemoveOneUniformlyStable_div`: the regime `β = κ / m` of
  Remark 13 (p. 507), with a gap of order `1 / √m`.

## Conventions and hypotheses

* Remove-one stability is the source's Definition 6 (p. 504), not the replace-one
  `IsUniformlyStable` (M. Hardt, B. Recht and Y. Singer, ICML 2016, Definition 2.1). The source
  writes the constant as `βm` and assumes it is non-increasing in sample size, so later
  arguments may bound the previous-size constant by the current one; this file fixes one size
  `m = n + 1` and formalizes inequality (11) (p. 507), whose proof does not use that convention.
* Following Sec. 2.1 (pp. 501-502), the source treats deterministic algorithms and assumes all
  functions are measurable and all sets are countable. Determinism is represented here by the
  function family `A`. The formal statements take the one joint-measurability hypothesis at
  size `n + 1` that the stated integrals and probabilities use, and no countability hypothesis.
* Boundedness `0 ≤ L (A (n + 1) S) z ≤ M` and joint measurability of `(S, z) ↦ L (A (n + 1) S) z`
  are assumed only at size `n + 1`; the source assumes boundedness for all samples `S`, so the
  hypothesis here is weaker. Joint measurability is added so that those probabilities and
  expectations take their intended values.
* Sec. 2.1 (pp. 501-502) assumes the algorithm does not depend on the order of the sample, and
  Lemma 7 is stated for symmetric learning algorithms. The formal statements take no symmetry
  hypothesis, because `abs_integral_empiricalRisk_sub_risk_le` gives the needed `2β`
  expectation step without one.
* `δ ∈ (0, 1)` as in the source. `0 < δ` is needed: at `δ = 0`, Lean's `log (1 / 0) = 0` would
  claim `R ≤ R_emp + 2β` almost surely.
* A constant `β` makes the bound vacuous, since
  `(4mβ + M) √(ln(1/δ) / (2m)) ≥ 2β √(2m ln(1/δ)) → ∞`. The useful regime is `β = κ / m`
  (`one_sub_le_measureReal_risk_le_of_isRemoveOneUniformlyStable_div`).

## Not formalized here

The leave-one-out inequality (12) of Theorem 12, hypothesis stability and pointwise hypothesis
stability (Definitions 3 and 4), and stability bounds for specific algorithms.
-/

@[expose] public section

open MeasureTheory Real

namespace CSLibExt.MachineLearning.GeneralizationBounds

/-- **Remove-one uniform stability** (Bousquet-Elisseeff, Definition 6, p. 504, at sample size
`n + 1`). The algorithm family `A` has remove-one uniform stability `β` for the loss `L` at size
`n + 1` if for every sample `S` of size `n + 1`, every index `i` and every test point `z`,
`|L (A (n + 1) S) z - L (A n (S \ i)) z| ≤ β`, where `S \ i = Fin.removeNth i S`. -/
def IsRemoveOneUniformlyStable {𝒵 H : Type*} (L : H → 𝒵 → ℝ)
    (A : (k : ℕ) → (Fin k → 𝒵) → H) (n : ℕ) (β : ℝ) : Prop :=
  ∀ (S : Fin (n + 1) → 𝒵) (i : Fin (n + 1)) (z : 𝒵),
    |L (A (n + 1) S) z - L (A n (Fin.removeNth i S)) z| ≤ β

/-- **Remove-one stability bounds replace-one changes by `2β`** (Bousquet-Elisseeff, remark
after Definition 6, p. 504). Replacing the `i`-th point of `S` by `z'` and then removing it
gives the same sample as removing it from `S` (`Fin.removeNth_update`), so the triangle
inequality through `A n (S \ i)` bounds the change of the loss at every test point by `2β`. -/
theorem abs_sub_le_two_mul_of_isRemoveOneUniformlyStable {𝒵 H : Type*} {L : H → 𝒵 → ℝ}
    {A : (k : ℕ) → (Fin k → 𝒵) → H} {n : ℕ} {β : ℝ}
    (hstab : IsRemoveOneUniformlyStable L A n β) (S : Fin (n + 1) → 𝒵) (i : Fin (n + 1))
    (z' z : 𝒵) :
    |L (A (n + 1) (Function.update S i z')) z - L (A (n + 1) S) z| ≤ 2 * β := by
  have h1 := hstab (Function.update S i z') i z
  have h2 := hstab S i z
  rw [Fin.removeNth_update] at h1
  have g1 := (abs_le.mp h1).1
  have g2 := (abs_le.mp h1).2
  have g3 := (abs_le.mp h2).1
  have g4 := (abs_le.mp h2).2
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith
  · linarith

/-- **Remove-one stability implies replace-one stability** (Bousquet-Elisseeff, remark after
Definition 6, p. 504). Remove-one uniform stability `β` at size `n + 1` implies replace-one uniform
stability `2β` (`IsUniformlyStable`) of the size-`(n + 1)` algorithm. -/
theorem isUniformlyStable_two_mul_of_isRemoveOneUniformlyStable {𝒵 H : Type*}
    {L : H → 𝒵 → ℝ} {A : (k : ℕ) → (Fin k → 𝒵) → H} {n : ℕ} {β : ℝ}
    (hstab : IsRemoveOneUniformlyStable L A n β) :
    IsUniformlyStable L (A (n + 1)) (2 * β) := by
  intro S i z' z
  exact (le_abs_self _).trans
    (abs_sub_le_two_mul_of_isRemoveOneUniformlyStable hstab S i z' z)

/-- **Tail form of Bousquet-Elisseeff Theorem 12** (the display in its proof on pp. 507-508,
before inequality (11)). For an i.i.d. sample `S ~ ν^m`, `m = n + 1`, a jointly measurable loss
with values in `[0, M]` and remove-one uniform stability `β`, for every `ε ≥ 0`,
`P[R(A_S) - R_emp(A_S) > ε + 2β] ≤ exp(-2mε² / (4mβ + M)²)`. When `4mβ + M = 0` the right-hand
side is read as `1` (Lean's `x / 0 = 0`). -/
theorem measureReal_lt_risk_sub_empiricalRisk_le_of_isRemoveOneUniformlyStable
    {𝒵 H : Type*} [MeasurableSpace 𝒵] {ν : Measure 𝒵} [IsProbabilityMeasure ν]
    {L : H → 𝒵 → ℝ} {A : (k : ℕ) → (Fin k → 𝒵) → H} {n : ℕ} {β M : ℝ}
    (hmeas : Measurable fun p : (Fin (n + 1) → 𝒵) × 𝒵 => L (A (n + 1) p.1) p.2)
    (hbdd : ∀ S z, 0 ≤ L (A (n + 1) S) z ∧ L (A (n + 1) S) z ≤ M)
    (hstab : IsRemoveOneUniformlyStable L A n β) {ε : ℝ} (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin (n + 1) => ν).real
        {S | ε + 2 * β < risk L ν (A (n + 1) S) - empiricalRisk L S (A (n + 1) S)} ≤
      exp (-2 * ((n : ℝ) + 1) * ε ^ 2 / (4 * ((n : ℝ) + 1) * β + M) ^ 2) := by
  set P : Measure (Fin (n + 1) → 𝒵) := Measure.pi fun _ : Fin (n + 1) => ν with hP
  set m : ℝ := ((n : ℝ) + 1) with hmdef
  set K : ℝ := 4 * m * β + M with hKdef
  have hm : 0 < m := by rw [hmdef]; positivity
  have hm0 : m ≠ 0 := ne_of_gt hm
  obtain ⟨z₀⟩ := ν.nonempty_of_neZero
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hstab (fun _ => z₀) 0 z₀)
  have hM : 0 ≤ M := (hbdd (fun _ => z₀) z₀).1.trans (hbdd (fun _ => z₀) z₀).2
  have hK : 0 ≤ K := by rw [hKdef]; positivity
  have hbdd' : ∀ S z, |L (A (n + 1) S) z| ≤ M := fun S z =>
    (abs_of_nonneg (hbdd S z).1).trans_le (hbdd S z).2
  have hem : |∫ S, (empiricalRisk L S (A (n + 1) S) -
      risk L ν (A (n + 1) S)) ∂P| ≤ 2 * β :=
    abs_integral_empiricalRisk_sub_risk_le (ν := ν) hmeas hbdd'
      (isUniformlyStable_two_mul_of_isRemoveOneUniformlyStable hstab)
  have hmean : ∫ S, (risk L ν (A (n + 1) S) -
      empiricalRisk L S (A (n + 1) S)) ∂P ≤ 2 * β := by
    have e : ∀ S : Fin (n + 1) → 𝒵, (risk L ν (A (n + 1) S) -
        empiricalRisk L S (A (n + 1) S)) =
        -(empiricalRisk L S (A (n + 1) S) - risk L ν (A (n + 1) S)) := fun S => by ring
    simp_rw [e, integral_neg]
    linarith [(abs_le.mp hem).1]
  have hKm : 0 ≤ K / m := by positivity
  set c : Fin (n + 1) → NNReal := fun _ => ⟨K / m, hKm⟩ with hcdef
  have hci : ∀ i : Fin (n + 1), ((c i : ℝ)) = K / m := fun i => rfl
  have hr : Measurable fun S : Fin (n + 1) → 𝒵 => risk L ν (A (n + 1) S) :=
    hmeas.stronglyMeasurable.integral_prod_right'.measurable
  have he : Measurable fun S : Fin (n + 1) → 𝒵 => empiricalRisk L S (A (n + 1) S) :=
    (Finset.measurable_sum _ fun i _ =>
      hmeas.comp (measurable_id.prodMk (measurable_pi_apply i))).const_mul _
  have hf : Measurable fun S : Fin (n + 1) → 𝒵 =>
      risk L ν (A (n + 1) S) - empiricalRisk L S (A (n + 1) S) := hr.sub he
  have hInt : ∀ S : Fin (n + 1) → 𝒵, Integrable (fun z => L (A (n + 1) S) z) ν := fun S =>
    Integrable.of_bound (hmeas.comp measurable_prodMk_left).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbdd S z).1]
        exact (hbdd S z).2)
  have hrisk_change : ∀ (S : Fin (n + 1) → 𝒵) (i : Fin (n + 1)) (z' : 𝒵),
      |risk L ν (A (n + 1) (Function.update S i z')) -
        risk L ν (A (n + 1) S)| ≤ 2 * β := by
    intro S i z'
    rw [risk, risk, ← integral_sub (hInt _) (hInt _)]
    simpa [Real.norm_eq_abs] using norm_integral_le_of_norm_le_const (μ := ν)
      (Filter.Eventually.of_forall fun z => (Real.norm_eq_abs _).trans_le
        (abs_sub_le_two_mul_of_isRemoveOneUniformlyStable hstab S i z' z))
  have h2β : (0:ℝ) ≤ 2 * β := by linarith [hβ]
  have hchanged : ∀ (S : Fin (n + 1) → 𝒵) (i : Fin (n + 1)) (z' : 𝒵),
      |L (A (n + 1) (Function.update S i z')) ((Function.update S i z') i) -
        L (A (n + 1) S) (S i)| ≤ M := by
    intro S i z'
    rw [Function.update_self]
    have c1 := (hbdd (Function.update S i z') z').1
    have c2 := (hbdd (Function.update S i z') z').2
    have c3 := (hbdd S (S i)).1
    have c4 := (hbdd S (S i)).2
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [c1, c2, c3, c4]
    · linarith [c1, c2, c3, c4]
  have hother : ∀ (S : Fin (n + 1) → 𝒵) (i : Fin (n + 1)) (z' : 𝒵) (j : Fin (n + 1)),
      j ≠ i → |L (A (n + 1) (Function.update S i z')) ((Function.update S i z') j) -
        L (A (n + 1) S) (S j)| ≤ 2 * β := by
    intro S i z' j hji
    rw [Function.update_of_ne hji]
    exact abs_sub_le_two_mul_of_isRemoveOneUniformlyStable hstab S i z' (S j)
  have hemp_change : ∀ (S : Fin (n + 1) → 𝒵) (i : Fin (n + 1)) (z' : 𝒵),
      |empiricalRisk L (Function.update S i z') (A (n + 1) (Function.update S i z')) -
        empiricalRisk L S (A (n + 1) S)| ≤ 2 * β + M / m := by
    intro S i z'
    simp only [empiricalRisk, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ))]
    calc (1 / ((n + 1 : ℕ) : ℝ)) * |∑ j, (L (A (n + 1) (Function.update S i z'))
            (Function.update S i z' j) - L (A (n + 1) S) (S j))|
        ≤ (1 / ((n + 1 : ℕ) : ℝ)) * ∑ j, (2 * β + if j = i then M else 0) := by
          gcongr
          refine (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun j _ => ?_)
          rcases eq_or_ne j i with rfl | hji
          · simpa using (hchanged S j z').trans (le_add_of_nonneg_left h2β)
          · simpa [hji] using hother S i z' j hji
      _ = 2 * β + M / m := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        push_cast
        rw [← hmdef]
        field_simp
  have hfc : ∀ (S : Fin (n + 1) → 𝒵) (i : Fin (n + 1)) (z' : 𝒵),
      |(risk L ν (A (n + 1) (Function.update S i z')) -
        empiricalRisk L (Function.update S i z')
          (A (n + 1) (Function.update S i z'))) -
        (risk L ν (A (n + 1) S) - empiricalRisk L S (A (n + 1) S))| ≤ ((c i : ℝ)) := by
    intro S i z'
    rw [hci i, hKdef, show (4 * m * β + M) / m = 4 * β + M / m by field_simp]
    have a1 := (abs_le.mp (hrisk_change S i z')).1
    have a2 := (abs_le.mp (hrisk_change S i z')).2
    have b1 := (abs_le.mp (hemp_change S i z')).1
    have b2 := (abs_le.mp (hemp_change S i z')).2
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [a1, b2]
    · linarith [a2, b1]
  have hsum : ∑ i : Fin (n + 1), ((c i : ℝ)) ^ 2 = K ^ 2 / m := by
    simp_rw [hci]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [← hmdef]
    field_simp
  have hexp : -2 * ε ^ 2 / ∑ i, ((c i : ℝ)) ^ 2 = -2 * m * ε ^ 2 / K ^ 2 := by
    rw [hsum]
    by_cases hK0 : K = 0
    · rw [hK0]
      simp
    · have hK20 : K ^ 2 ≠ 0 := pow_ne_zero 2 hK0
      field_simp
  have htail := ProbabilityTheory.measureReal_sub_integral_ge_le_of_bounded_differences
    (μ := fun _ : Fin (n + 1) => ν) hf hfc hε
  rw [← hP, hexp] at htail
  refine (measureReal_mono (fun S hS => ?_)).trans htail
  simp only [Set.mem_ofPred_eq] at hS ⊢
  linarith [hmean, hS]

/-- **Uniform stability implies high-probability generalization** (Bousquet-Elisseeff,
Theorem 12, inequality (11), p. 507). For an i.i.d. sample `S ~ ν^m`, `m = n + 1`, a jointly
measurable loss with values in `[0, M]` and remove-one uniform stability `β`, for every
`δ ∈ (0, 1)`, with probability at least `1 - δ`,
`R(A_S) ≤ R_emp(A_S) + 2β + (4mβ + M) √(ln(1/δ) / (2m))`. -/
theorem one_sub_le_measureReal_risk_le_of_isRemoveOneUniformlyStable
    {𝒵 H : Type*} [MeasurableSpace 𝒵] {ν : Measure 𝒵} [IsProbabilityMeasure ν]
    {L : H → 𝒵 → ℝ} {A : (k : ℕ) → (Fin k → 𝒵) → H} {n : ℕ} {β M : ℝ}
    (hmeas : Measurable fun p : (Fin (n + 1) → 𝒵) × 𝒵 => L (A (n + 1) p.1) p.2)
    (hbdd : ∀ S z, 0 ≤ L (A (n + 1) S) z ∧ L (A (n + 1) S) z ≤ M)
    (hstab : IsRemoveOneUniformlyStable L A n β) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin (n + 1) => ν).real
      {S | risk L ν (A (n + 1) S) ≤ empiricalRisk L S (A (n + 1) S) + 2 * β +
        (4 * ((n : ℝ) + 1) * β + M) * √(log (1 / δ) / (2 * ((n : ℝ) + 1)))} := by
  set P : Measure (Fin (n + 1) → 𝒵) := Measure.pi fun _ : Fin (n + 1) => ν with hP
  set m : ℝ := ((n : ℝ) + 1) with hmdef
  set K : ℝ := 4 * m * β + M with hKdef
  have hm : 0 < m := by rw [hmdef]; positivity
  have hm0 : m ≠ 0 := ne_of_gt hm
  obtain ⟨z₀⟩ := ν.nonempty_of_neZero
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hstab (fun _ => z₀) 0 z₀)
  have hM : 0 ≤ M := (hbdd (fun _ => z₀) z₀).1.trans (hbdd (fun _ => z₀) z₀).2
  have hK : 0 ≤ K := by rw [hKdef]; positivity
  by_cases hK0 : K = 0
  · have h4m : (0 : ℝ) ≤ 4 * m * β := by positivity
    have hβ0 : β = 0 := by
      have h1 : 4 * m * β = 0 := by linarith
      have h4m0 : (4 : ℝ) * m ≠ 0 := ne_of_gt (by positivity)
      exact (mul_eq_zero.mp h1).resolve_left h4m0
    have hM0 : M = 0 := by linarith
    have hloss : ∀ S z, L (A (n + 1) S) z = 0 := fun S z => by
      have h2 := (hbdd S z).2
      rw [hM0] at h2
      exact le_antisymm h2 (hbdd S z).1
    have hrisk : ∀ S, risk L ν (A (n + 1) S) = 0 := fun S => by
      simp [risk, hloss S]
    have hemp : ∀ S, empiricalRisk L S (A (n + 1) S) = 0 := fun S => by
      simp [empiricalRisk, hloss S]
    have hmem : ∀ S : Fin (n + 1) → 𝒵, S ∈ {S | risk L ν (A (n + 1) S) ≤
        empiricalRisk L S (A (n + 1) S) + 2 * β + K * √(log (1 / δ) / (2 * m))} := by
      intro S
      simp only [Set.mem_ofPred_eq]
      rw [hrisk S, hemp S, hβ0, hK0]
      simp
    have h2 := measureReal_mono (μ := P) (fun S (_ : S ∈ Set.univ) => hmem S)
    rw [probReal_univ] at h2
    have hδle : (1 : ℝ) - δ ≤ 1 := by linarith
    exact hδle.trans h2
  · have hlogδ : log δ ≤ 0 := Real.log_nonpos (le_of_lt hδ0) (le_of_lt hδ1)
    have hL : log (1 / δ) = -log δ := by
      rw [Real.log_div one_ne_zero (ne_of_gt hδ0), Real.log_one, zero_sub]
    have hlog : 0 ≤ log (1 / δ) := by rw [hL]; linarith
    have hnn : 0 ≤ log (1 / δ) / (2 * m) := by positivity
    set ε : ℝ := K * √(log (1 / δ) / (2 * m)) with hεdef
    have hε : 0 ≤ ε := by rw [hεdef]; positivity
    have htail := measureReal_lt_risk_sub_empiricalRisk_le_of_isRemoveOneUniformlyStable
      (ν := ν) hmeas hbdd hstab (ε := ε) hε
    rw [← hP, ← hmdef, ← hKdef] at htail
    have hε2 : ε ^ 2 = K ^ 2 * (log (1 / δ) / (2 * m)) := by
      rw [hεdef, mul_pow, Real.sq_sqrt hnn]
    have hK20 : K ^ 2 ≠ 0 := pow_ne_zero 2 hK0
    have h2m : (2 : ℝ) * m ≠ 0 := mul_ne_zero two_ne_zero hm0
    have hexp : -2 * m * ε ^ 2 / K ^ 2 = log δ := by
      rw [hε2, hL]
      field_simp
    rw [hexp, Real.exp_log hδ0] at htail
    have hmem : ∀ S : Fin (n + 1) → 𝒵, S ∈ ({S | risk L ν (A (n + 1) S) ≤
        empiricalRisk L S (A (n + 1) S) + 2 * β + ε} ∪
        {S | ε + 2 * β < risk L ν (A (n + 1) S) -
          empiricalRisk L S (A (n + 1) S)}) := by
      intro S
      by_cases h : ε + 2 * β <
        risk L ν (A (n + 1) S) - empiricalRisk L S (A (n + 1) S)
      · exact Or.inr h
      · refine Or.inl ?_
        simp only [Set.mem_ofPred_eq]
        have hle := le_of_not_gt h
        linarith
    have h2 := (measureReal_mono (μ := P) (fun S (_ : S ∈ Set.univ) => hmem S)).trans
      (measureReal_union_le (μ := P) _ _)
    rw [probReal_univ] at h2
    linarith

/-- **The `β = κ / m` regime** (Bousquet-Elisseeff, Remark 13, p. 507). If the remove-one uniform
stability at size `m = n + 1` is `κ / m`, then with probability at least `1 - δ`,
`R(A_S) ≤ R_emp(A_S) + 2κ / m + (4κ + M) √(ln(1/δ) / (2m))`, a gap of order `1 / √m`. -/
theorem one_sub_le_measureReal_risk_le_of_isRemoveOneUniformlyStable_div
    {𝒵 H : Type*} [MeasurableSpace 𝒵] {ν : Measure 𝒵} [IsProbabilityMeasure ν]
    {L : H → 𝒵 → ℝ} {A : (k : ℕ) → (Fin k → 𝒵) → H} {n : ℕ} {κ M : ℝ}
    (hmeas : Measurable fun p : (Fin (n + 1) → 𝒵) × 𝒵 => L (A (n + 1) p.1) p.2)
    (hbdd : ∀ S z, 0 ≤ L (A (n + 1) S) z ∧ L (A (n + 1) S) z ≤ M)
    (hstab : IsRemoveOneUniformlyStable L A n (κ / ((n : ℝ) + 1))) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    1 - δ ≤ (Measure.pi fun _ : Fin (n + 1) => ν).real
      {S | risk L ν (A (n + 1) S) ≤ empiricalRisk L S (A (n + 1) S) + 2 * κ / ((n : ℝ) + 1) +
        (4 * κ + M) * √(log (1 / δ) / (2 * ((n : ℝ) + 1)))} := by
  have hm0 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
  have hmain := one_sub_le_measureReal_risk_le_of_isRemoveOneUniformlyStable (ν := ν)
    hmeas hbdd hstab hδ0 hδ1
  have e1 : 2 * (κ / ((n : ℝ) + 1)) = 2 * κ / ((n : ℝ) + 1) := by ring
  have e2 : 4 * ((n : ℝ) + 1) * (κ / ((n : ℝ) + 1)) + M = 4 * κ + M := by
    field_simp
  rw [e1, e2] at hmain
  exact hmain

end CSLibExt.MachineLearning.GeneralizationBounds
