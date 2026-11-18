/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GeneralizationBounds.FiniteClass
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Uniform stability implies generalization in expectation

An algorithm `A` maps a sample `S = (z₁, …, zₙ)` to a predictor `A(S)`. It is `ε`-uniformly stable
if replacing one example of the sample changes the loss at any test point by at most `ε`
(M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic
gradient descent*, ICML 2016, arXiv:1509.01240, Definition 2.1; O. Bousquet and A. Elisseeff,
*Stability and generalization*, JMLR 2 (2002)). For an i.i.d. sample, the expected generalization
gap `E_S[R̂_S(A(S)) - R(A(S))]` is then at most `ε` in absolute value (Hardt–Recht–Singer,
Theorem 2.2). The proof exchanges a training example with a fresh one: replacing the `i`-th
coordinate of `S` by an independent `z ~ ν` leaves the law of the sample unchanged
(`map_update_prod_pi`).

Unlike uniform-convergence bounds over a class
(`measureReal_exists_abs_empiricalRisk_sub_risk_ge_le`, Rademacher complexity), the bound
involves only the algorithm's sensitivity to its sample, not the size or complexity of the class
of predictors it may output.

## Main definitions

- `IsUniformlyStable L A ε`: replace-one uniform stability of a (deterministic) algorithm.

## Main results

- `map_update_prod_pi`: replacing one coordinate of an i.i.d. sample by an independent copy
  preserves its law.
- `abs_integral_empiricalRisk_sub_risk_le`: uniform stability bounds the expected generalization
  gap, for a jointly measurable bounded loss.

## Hypotheses

The source states Theorem 2.2 without regularity hypotheses. Here the loss profile
`(S, z) ↦ L (A S) z` is assumed jointly measurable and bounded. Joint measurability makes the
evaluation of the loss at a training point, `S ↦ L (A S) (S i)`, measurable; boundedness makes every
expectation in the proof finite.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace CSLibExt.MachineLearning.GeneralizationBounds

variable {𝒵 H : Type*} [MeasurableSpace 𝒵]

/-- **Uniform stability.** An algorithm `A`, mapping a sample `S : Fin n → 𝒵` to a predictor
`A S`, is `ε`-uniformly stable for the loss `L` if for every sample `S`, every index `i`, every
replacement example `z'` and every test example `z`,
`L (A S') z - L (A S) z ≤ ε` where `S' = Function.update S i z'` is `S` with its `i`-th example
replaced by `z'`. The samples `S` and `S'` range over all pairs differing in at most one example,
so the one-sided bound also holds with the roles of `S` and `S'` exchanged.

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Definition 2.1, for an algorithm without
internal randomness (for a randomized algorithm, take `L (A S) z` to be the expected loss over the
internal randomness). -/
def IsUniformlyStable {n : ℕ} (L : H → 𝒵 → ℝ) (A : (Fin n → 𝒵) → H) (ε : ℝ) : Prop :=
  ∀ (S : Fin n → 𝒵) (i : Fin n) (z' z : 𝒵), L (A (Function.update S i z')) z - L (A S) z ≤ ε

/-- **Replace-one sampling preserves the law of an i.i.d. sample.** If `S ~ ν^{⊗n}` and `z ~ ν`
are independent, then the sample `Function.update S i z`, which is `S` with its `i`-th example
replaced by `z`, again has law `ν^{⊗n}`.

Source: the exchange step in the proof of Theorem 2.2 of M. Hardt, B. Recht and Y. Singer,
*Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016,
arXiv:1509.01240 (the sample `S⁽ⁱ⁾` built from independent samples `S` and `S'`). -/
theorem map_update_prod_pi {n : ℕ} (ν : Measure 𝒵) [IsProbabilityMeasure ν] (i : Fin n) :
    ((Measure.pi fun _ : Fin n => ν).prod ν).map (fun p => Function.update p.1 i p.2) =
      Measure.pi fun _ : Fin n => ν := by
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin n → 𝒵) × 𝒵 => Function.update p.1 i p.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi (Function.update s i Set.univ) ×ˢ s i := by
    ext ⟨S, z⟩
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun j => ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; simpa using h2
      · simpa [Function.update_of_ne hj] using h1 j
  rw [hpre, Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ (fun j => ν (s j)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => ν (Function.update s i Set.univ j))
      (Finset.mem_univ i)]
  simp only [Function.update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **Uniform stability implies generalization in expectation.** Let `ν` be a probability measure
on the example space, let `S ~ ν^{⊗n}` be an i.i.d. sample of size `n ≥ 1`, and let the algorithm
`A` be `ε`-uniformly stable (`IsUniformlyStable`) for a loss `L` such that `(S, z) ↦ L (A S) z` is
jointly measurable and bounded. Then the expected generalization gap is at most `ε`:
`|E_S[R̂_S(A(S)) - R(A(S))]| ≤ ε`, where `R̂_S = empiricalRisk L S` and `R = risk L ν`.

Source: M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of
stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Theorem 2.2 (stated there without
regularity hypotheses; joint measurability and boundedness of the loss are added here so that
every expectation is defined and finite), after O. Bousquet and A. Elisseeff, *Stability and
generalization*, JMLR 2 (2002). -/
theorem abs_integral_empiricalRisk_sub_risk_le {ν : Measure 𝒵} [IsProbabilityMeasure ν] {n : ℕ}
    (hn : 0 < n) {L : H → 𝒵 → ℝ} {A : (Fin n → 𝒵) → H}
    (hmeas : Measurable fun p : (Fin n → 𝒵) × 𝒵 => L (A p.1) p.2) {M : ℝ}
    (hbdd : ∀ S z, |L (A S) z| ≤ M) {ε : ℝ} (hstab : IsUniformlyStable L A ε) :
    |∫ S, (empiricalRisk L S (A S) - risk L ν (A S)) ∂(Measure.pi fun _ : Fin n => ν)| ≤ ε := by
  set P : Measure (Fin n → 𝒵) := Measure.pi fun _ : Fin n => ν with hP
  set Q : Measure ((Fin n → 𝒵) × 𝒵) := P.prod ν with hQ
  -- measurability of the loss at a training point and at a replaced sample
  have hdiag : ∀ i : Fin n, Measurable fun S : Fin n → 𝒵 => L (A S) (S i) := fun i =>
    hmeas.comp (measurable_id.prodMk (measurable_pi_apply i))
  have hrepl : ∀ i : Fin n,
      Measurable fun p : (Fin n → 𝒵) × 𝒵 => L (A (Function.update p.1 i p.2)) p.2 := fun i =>
    hmeas.comp (measurable_update'.prodMk measurable_snd)
  have hbddQ : ∀ (f : (Fin n → 𝒵) × 𝒵 → ℝ), Measurable f → (∀ p, |f p| ≤ M) →
      Integrable f Q := fun f hf hb =>
    Integrable.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall fun p => by
      simpa [Real.norm_eq_abs] using hb p)
  have hgQ : Integrable (fun p : (Fin n → 𝒵) × 𝒵 => L (A p.1) p.2) Q :=
    hbddQ _ hmeas fun p => hbdd _ _
  have hrQ : ∀ i,
      Integrable (fun p : (Fin n → 𝒵) × 𝒵 => L (A (Function.update p.1 i p.2)) p.2) Q :=
    fun i => hbddQ _ (hrepl i) fun p => hbdd _ _
  have hdiagP : ∀ i, Integrable (fun S : Fin n → 𝒵 => L (A S) (S i)) P := fun i =>
    Integrable.of_bound (hdiag i).aestronglyMeasurable M (Filter.Eventually.of_forall fun S => by
      simpa [Real.norm_eq_abs] using hbdd S (S i))
  -- the risk term, by Fubini
  have hriskP : Integrable (fun S : Fin n → 𝒵 => risk L ν (A S)) P := by
    have := hgQ.integral_prod_left
    simpa [risk] using this
  have hrisk : ∫ S, risk L ν (A S) ∂P = ∫ p, L (A p.1) p.2 ∂Q := by
    rw [integral_prod _ hgQ]
    rfl
  -- the exchange step: the training-point loss has the same mean as the replaced-sample loss
  have hexch : ∀ i, ∫ S, L (A S) (S i) ∂P = ∫ p, L (A (Function.update p.1 i p.2)) p.2 ∂Q := by
    intro i
    have h := integral_map (μ := Q) (φ := fun p : (Fin n → 𝒵) × 𝒵 => Function.update p.1 i p.2)
      measurable_update'.aemeasurable (f := fun S : Fin n → 𝒵 => L (A S) (S i))
      (by rw [hQ, hP, map_update_prod_pi ν i]; exact (hdiag i).aestronglyMeasurable)
    rw [hQ, hP, map_update_prod_pi ν i] at h
    rw [hP, h]
    simp [Function.update_self, hQ, hP]
  -- empirical risk as an average of training-point losses
  have hemp : ∫ S, empiricalRisk L S (A S) ∂P = (1 / n : ℝ) * ∑ i, ∫ S, L (A S) (S i) ∂P := by
    simp only [empiricalRisk]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hdiagP i]
  have hempI : Integrable (fun S : Fin n → 𝒵 => empiricalRisk L S (A S)) P := by
    simp only [empiricalRisk]
    exact (integrable_finsetSum _ fun i _ => hdiagP i).const_mul _
  -- pointwise two-sided stability
  have hpt : ∀ i (p : (Fin n → 𝒵) × 𝒵),
      ‖L (A (Function.update p.1 i p.2)) p.2 - L (A p.1) p.2‖ ≤ ε := by
    intro i ⟨S, z⟩
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨?_, hstab S i z z⟩
    have h := hstab (Function.update S i z) i (S i) z
    rw [Function.update_idem, Function.update_eq_self] at h
    linarith
  have hterm : ∀ i, |∫ p, (L (A (Function.update p.1 i p.2)) p.2 - L (A p.1) p.2) ∂Q| ≤ ε := by
    intro i
    have h := norm_integral_le_of_norm_le_const (μ := Q) (Filter.Eventually.of_forall (hpt i))
    simpa [Real.norm_eq_abs, hQ] using h
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hdecomp : ∫ S, (empiricalRisk L S (A S) - risk L ν (A S)) ∂P =
      (1 / n : ℝ) * ∑ i, ∫ p, (L (A (Function.update p.1 i p.2)) p.2 - L (A p.1) p.2) ∂Q := by
    rw [integral_sub hempI hriskP, hemp, hrisk]
    simp only [hexch]
    rw [Finset.mul_sum, Finset.mul_sum]
    have : ∫ p, L (A p.1) p.2 ∂Q =
        ∑ _i : Fin n, (1 / n : ℝ) * ∫ p, L (A p.1) p.2 ∂Q := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    rw [this, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_sub (hrQ i) hgQ]
    ring
  rw [hdecomp, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / n)]
  calc (1 / n : ℝ) * |∑ i, ∫ p, (L (A (Function.update p.1 i p.2)) p.2 - L (A p.1) p.2) ∂Q|
      ≤ (1 / n : ℝ) * ∑ _i : Fin n, ε := by
        gcongr
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hterm i)
    _ = ε := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

end CSLibExt.MachineLearning.GeneralizationBounds
