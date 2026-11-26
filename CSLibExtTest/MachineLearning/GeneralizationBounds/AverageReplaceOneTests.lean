/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GeneralizationBounds.AverageReplaceOne
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

open MeasureTheory ProbabilityTheory

namespace CSLibExt.MachineLearning.GeneralizationBounds

-- A seed-dependent learner that ignores its sample has zero replacement difference at every draw.
example {𝒵 H R : Type*} [MeasurableSpace 𝒵] [MeasurableSpace R] {m : ℕ} [NeZero m]
    (L : H → 𝒵 → ℝ) (a : R → H) (ρ : Measure R) [IsProbabilityMeasure ρ] :
    IsOnAverageReplaceOneStable (m := m) L (fun _ => a) ρ 0 := by
  unfold IsOnAverageReplaceOneStable
  intro ν _
  dsimp only
  intro _ _
  simp

-- A uniform bound for every seed implies the average bound; the conclusion still uses
-- the actual signed difference under the joint probability law.
example {𝒵 H R : Type*} [MeasurableSpace 𝒵] [MeasurableSpace R] {m : ℕ} [NeZero m]
    (L : H → 𝒵 → ℝ) (A : (Fin m → 𝒵) → R → H) (ρ : Measure R) [IsProbabilityMeasure ρ]
    (ε : ℝ) (h : ∀ r, IsUniformlyStable L (fun S => A S r) ε) :
    IsOnAverageReplaceOneStable L A ρ ε := by
  unfold IsOnAverageReplaceOneStable
  intro ν _
  dsimp only
  intro hreplaced horiginal
  calc
    _ ≤ ∫ _ : (Fin m → 𝒵) × 𝒵 × Fin m × R, ε
        ∂((Measure.pi fun _ : Fin m => ν).prod
          (ν.prod ((uniformOn (Set.univ : Set (Fin m))).prod ρ))) :=
      integral_mono (hreplaced.sub horiginal) (integrable_const ε) fun ⟨S, z', i, r⟩ =>
        h r S i z' (S i)
    _ = ε := by simp

-- For the opposite loss, replacing a bit can only decrease the loss at the original point.
-- The signed bound is zero even though the two losses need not be equal.
example : IsOnAverageReplaceOneStable
    (fun (w z : Fin 2) => if w = z then (1 : ℝ) else 0)
    (fun (S : Fin 1 → Fin 2) (_ : Fin 1) => S 0) (uniformOn Set.univ) 0 := by
  unfold IsOnAverageReplaceOneStable
  intro ν _
  dsimp only
  intro _ _
  apply integral_nonpos
  rintro ⟨S, z', i, r⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp only [Function.update_self]
  split <;> norm_num

-- At size one, remembering the bit incurs mean replacement loss 1/2 under fair bits,
-- while the original loss is zero. In particular the learner is not 0-stable.
example : ¬ IsOnAverageReplaceOneStable
    (fun (w z : Fin 2) => if w = z then (0 : ℝ) else 1)
    (fun (S : Fin 1 → Fin 2) (_ : Fin 1) => S 0) (uniformOn Set.univ) 0 := by
  let ν : Measure (Fin 2) := uniformOn Set.univ
  let ρ : Measure (Fin 1) := uniformOn Set.univ
  let μ := (Measure.pi fun _ : Fin 1 => ν).prod (ν.prod (ρ.prod ρ))
  let replaced : (Fin 1 → Fin 2) × Fin 2 × Fin 1 × Fin 1 → ℝ :=
    fun (S, z', i, _) => if Function.update S i z' 0 = S i then 0 else 1
  have hreplaced : Integrable replaced μ := by
    apply Integrable.of_bound (measurable_of_finite replaced).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ⟨S, z', i, r⟩ => by
      change ‖(if Function.update S i z' 0 = S i then (0 : ℝ) else 1)‖ ≤ 1
      split <;> simp
  have horiginal : Integrable (fun (x : (Fin 1 → Fin 2) × Fin 2 × Fin 1 × Fin 1) =>
      if x.1 0 = x.1 x.2.2.1 then (0 : ℝ) else 1) μ := by
    convert (integrable_const (μ := μ) (0 : ℝ)) using 1
    ext x
    simp [Subsingleton.elim (0 : Fin 1) x.2.2.1]
  intro h
  have hle := h ν hreplaced horiginal
  have hle' : (∫ x, replaced x ∂μ) ≤ 0 := by
    simpa [IsOnAverageReplaceOneStable, replaced, μ, ρ, Subsingleton.elim (_ : Fin 1) 0] using hle
  have prod_singleton {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
      (μ₁ : Measure α) (μ₂ : Measure β) [SFinite μ₂] (a : α) (b : β) :
      (μ₁.prod μ₂) {(a, b)} = μ₁ {a} * μ₂ {b} := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  have hmass (x : (Fin 1 → Fin 2) × Fin 2 × Fin 1 × Fin 1) : μ.real {x} = 1 / 4 := by
    rcases x with ⟨S, z', i, r⟩
    simp only [measureReal_def, μ, prod_singleton, Measure.pi_singleton, Fin.prod_univ_one]
    norm_num [ν, ρ, uniformOn_univ, Measure.count_singleton, Fintype.card_fin,
      ENNReal.toReal_mul, ENNReal.toReal_div]
  have heval : (∫ x, replaced x ∂μ) = 1 / 2 := by
    rw [integral_fintype hreplaced]
    simp only [hmass, smul_eq_mul, Fintype.sum_prod_type, Fintype.sum_unique]
    have hi (i : Fin 1) : i = 0 := Subsingleton.elim _ _
    have hinner (a : Fin 2) : (∑ b : Fin 2, (1 / 4 : ℝ) * if b = a then 0 else 1) = 1 / 4 := by
      fin_cases a <;> norm_num [Fin.sum_univ_two]
    simp only [replaced, hi, Function.update_self, hinner, Finset.sum_const, Finset.card_univ]
    norm_num [Fintype.card_fun, Fintype.card_fin]
  linarith

end CSLibExt.MachineLearning.GeneralizationBounds
