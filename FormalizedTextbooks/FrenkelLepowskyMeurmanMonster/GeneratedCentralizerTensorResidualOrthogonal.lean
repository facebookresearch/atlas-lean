/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual tensor residual has an orthogonal spin factor. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensorResidual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TensorColumnOrthogonality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem realZeroDot {ι : Type*} [Fintype ι] :
    (∑ r : ι, (0 : ι → ℝ) r * (0 : ι → ℝ) r) = 0 := by
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]

/-- The actual negative-space form is the unscaled ordinary tensor-coordinate pairing. -/
theorem generatedCentralMinus_griessForm_tensorPairing (x y : generatedCentralMinus) :
    griessForm x.val y.val =
      tensorColumnPairing (generatedCentralMinusTensorEquiv x)
        (generatedCentralMinusTensorEquiv y) := by
  have hx := (mem_generatedCentralMinus_iff_matrix_short_zero x.val).mp x.property
  have hy := (mem_generatedCentralMinus_iff_matrix_short_zero y.val).mp y.property
  rw [griessForm_eq_conwayRawForm, conwayRawForm, hx.1, hx.2, hy.1, hy.2, realZeroDot]
  simp only [conwayMatrixForm_eq_sum, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    zero_add, add_zero]
  rfl

/-- The genuine centralizer tensor action preserves its original real coordinate pairing. -/
theorem generatedCentralizerTensorAction_pairing (g : generatedCentralizer)
    (T U : SpinIndex → Fin 24 → ℝ) :
    tensorColumnPairing (generatedCentralizerTensorAction g T)
      (generatedCentralizerTensorAction g U) = tensorColumnPairing T U := by
  obtain ⟨x, rfl⟩ := generatedCentralMinusTensorEquiv.surjective T
  obtain ⟨y, rfl⟩ := generatedCentralMinusTensorEquiv.surjective U
  rw [generatedCentralizerTensorAction_intertwines, generatedCentralizerTensorAction_intertwines,
    ← generatedCentralMinus_griessForm_tensorPairing,
    ← generatedCentralMinus_griessForm_tensorPairing]
  exact generated_group_preserves_griessForm g.val x.val y.val

/-- Any common spin column factor of the actual centralizer is an orthogonal equivalence. -/
theorem generatedCentralizerTensorAction_spin_equiv (g : generatedCentralizer)
    (S : Module.End ℝ SpinSpace)
    (hS : ∀ (T : SpinIndex → Fin 24 → ℝ) t i,
      generatedCentralizerTensorAction g T t i = S (fun u => T u i) t) :
    ∃ e : SpinSpace ≃ₗ[ℝ] SpinSpace, e.toLinearMap = S ∧ e ∈ spinOrthogonalSubgroup := by
  exact tensorColumnwise_spin_equiv (generatedCentralizerTensorAction g).toLinearMap S hS
    (generatedCentralizerTensorAction_pairing g)

/-- Every genuine matrix-fixing residual has an orthogonal spin factor on all tensor columns. -/
theorem generatedCentralizerTensorAction_orthogonal_spin_columns (g : generatedCentralizer)
    (hfix : ∀ A : Sym24, g.val.val (generatedCentralPlusEmbed A 0).val =
      (generatedCentralPlusEmbed A 0).val) :
    ∃ e : SpinSpace ≃ₗ[ℝ] SpinSpace, e ∈ spinOrthogonalSubgroup ∧
      ∀ (T : SpinIndex → Fin 24 → ℝ) t i,
        generatedCentralizerTensorAction g T t i = e (fun u => T u i) t := by
  obtain ⟨S, hS⟩ := generatedCentralizerTensorAction_spin_columns g hfix
  obtain ⟨e, he, hoe⟩ := generatedCentralizerTensorAction_spin_equiv g S hS
  refine ⟨e, hoe, ?_⟩
  intro T t i
  rw [hS, ← he]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
