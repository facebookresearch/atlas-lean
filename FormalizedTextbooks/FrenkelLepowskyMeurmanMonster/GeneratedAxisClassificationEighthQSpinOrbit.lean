/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationEighthQPauliState
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.FiniteCoordinateOrbitNormBound

/-! Eleven independent actual fixing translations bound every genuine spin coefficient. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The genuine extraspecial stabilizer of the actual middle spin state. -/
def generatedEighthSpinStateStabilizer : Subgroup Q :=
  MulAction.stabilizer Q generatedEighthSpinState

/-- Products of the eleven selected original Pauli elements, with literal binary exponents. -/
def generatedEighthSpinPauliProduct (a : Fin 11 → ZMod 2) : Q :=
  (List.ofFn (fun j : Fin 11 =>
    (generatedEighthSpinPauliCache (generatedEighthSpinPauliIndependent j) 7) ^ (a j).val)).prod

/-- Each product genuinely fixes the original middle spin state. -/
theorem generatedEighth_spin_pauli_product_fixed (a : Fin 11 → ZMod 2) :
    spinRepresentation (generatedEighthSpinPauliProduct a) generatedEighthSpinState =
      generatedEighthSpinState := by
  change generatedEighthSpinPauliProduct a ∈ generatedEighthSpinStateStabilizer
  apply generatedEighthSpinStateStabilizer.list_prod_mem
  intro q hq
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hq
  apply generatedEighthSpinStateStabilizer.pow_mem
  exact generatedEighth_spin_pauli_final_fixed (generatedEighthSpinPauliIndependent j)

private theorem translation_prod (l : List Q) :
    spinTranslation l.prod = (l.map spinTranslation).sum := by
  induction l with
  | nil => rfl
  | cons q l ih => simp only [List.prod_cons, spinTranslation_mul, ih, List.map_cons,
      List.sum_cons]

private theorem translation_pow (q : Q) (n : ℕ) :
    spinTranslation (q ^ n) = n • spinTranslation q := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ, spinTranslation_mul, ih, succ_nsmul]

private theorem translation_binary_pow (q : Q) (b : ZMod 2) :
    spinTranslation (q ^ b.val) = b • spinTranslation q := by
  rw [translation_pow, ← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_val, ZMod.cast_id]

/-- The true Pauli products have exactly the certified rank-eleven translation matrix. -/
theorem generatedEighth_spin_pauli_product_translation (a : Fin 11 → ZMod 2) :
    spinTranslation (generatedEighthSpinPauliProduct a) =
      generatedEighthSpinPauliTranslationMatrix *ᵥ a := by
  unfold generatedEighthSpinPauliProduct
  rw [translation_prod, List.map_ofFn, List.sum_ofFn]
  funext i
  simp only [Finset.sum_apply, Function.comp_apply, translation_binary_pow,
    Pi.smul_apply, smul_eq_mul, generatedEighth_spin_pauli_translation_coordinate,
    Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The eleven original translation columns give an injective genuine binary action. -/
theorem generatedEighth_spin_translation_matrix_injective :
    Function.Injective (fun a : Fin 11 → ZMod 2 =>
      generatedEighthSpinPauliTranslationMatrix *ᵥ a) := by
  intro a b h
  have he := congrArg (fun v => generatedEighthSpinPauliLeftInverse *ᵥ v) h
  simpa only [Matrix.mulVec_mulVec, generatedEighth_spin_pauli_left_inverse,
    Matrix.one_mulVec] using he

/-- Every fixed-coordinate orbit contains 2048 distinct genuine spin indices. -/
def generatedEighthSpinCoordinateOrbit (t : SpinIndex) : (Fin 11 → ZMod 2) ↪ SpinIndex where
  toFun a := t + spinTranslation (generatedEighthSpinPauliProduct a)
  inj' := by
    intro a b h
    apply generatedEighth_spin_translation_matrix_injective
    exact (generatedEighth_spin_pauli_product_translation a).symm.trans
      ((add_left_cancel h).trans (generatedEighth_spin_pauli_product_translation b))

private theorem coordinate_orbit_apply (t : SpinIndex) (a : Fin 11 → ZMod 2) :
    generatedEighthSpinCoordinateOrbit t a =
      t + spinTranslation (generatedEighthSpinPauliProduct a) := rfl

private theorem fixed_square (q : Q) (f : SpinSpace)
    (hf : spinRepresentation q f = f) (t : SpinIndex) :
    (f (t + spinTranslation q)) ^ 2 = (f t) ^ 2 := by
  have h := (generatedSpinSupport_fixed_iff q f).mp hf t
  have hs := congrArg (fun z : ℝ => z ^ 2) h
  rw [mul_pow] at hs
  have hsign : (qSign (spinPhase q t)) ^ 2 = 1 := by rw [pow_two, qSign_sq]
  rw [hsign, one_mul] at hs
  exact hs

/-- Fixation retains the square of every actual translated spin coefficient. -/
theorem generatedEighth_spin_coordinate_orbit_square (t : SpinIndex) (a : Fin 11 → ZMod 2) :
    (generatedEighthSpinState (generatedEighthSpinCoordinateOrbit t a)) ^ 2 =
      (generatedEighthSpinState t) ^ 2 := by
  rw [coordinate_orbit_apply]
  exact fixed_square (generatedEighthSpinPauliProduct a) generatedEighthSpinState
    (generatedEighth_spin_pauli_product_fixed a) t

/-- The norm-two state and its 2048 genuine equal-square translates bound every coefficient. -/
theorem generatedEighth_spin_state_square_bound (t : SpinIndex) :
    (generatedEighthSpinState t) ^ 2 ≤ (1 / 1024 : ℝ) := by
  have he := finiteCoordinateOrbitNormBound_of_finite
    (generatedEighthSpinCoordinateOrbit t) generatedEighthSpinState t
    (generatedEighth_spin_coordinate_orbit_square t)
  have hc : Nat.card (Fin 11 → ZMod 2) = 2048 := by
    norm_num [Nat.card_eq_fintype_card, ZMod.card]
  rw [hc] at he
  simp only [pow_two] at he
  change (2048 : ℝ) * (generatedEighthSpinState t * generatedEighthSpinState t) ≤
    spinPairing generatedEighthSpinState generatedEighthSpinState at he
  rw [generatedEighth_spin_state_pairing] at he
  nlinarith only [he]

/-- The two original Ω coordinates have a bounded difference because their supports are disjoint. -/
theorem generatedEighth_spin_state_omega_difference_bound (t : SpinIndex) :
    (generatedEighthSpinState t -
      generatedEighthSpinState (t + Pi.single (11 : Fin 12) 1)) ^ 2 ≤ (1 / 1024 : ℝ) := by
  by_cases ht : generatedEighthSpinState t = 0
  · rw [ht, zero_sub, neg_sq]
    exact generatedEighth_spin_state_square_bound _
  · have hu := (mul_eq_zero.mp (generatedEighth_spin_state_omega_product_zero t)).resolve_left ht
    rw [hu, sub_zero]
    exact generatedEighth_spin_state_square_bound t

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
