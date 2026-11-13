/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Stoichiometry.Balance

/-!

# Tests for stoichiometric balance and reaction extents

-/

@[expose] public section

open Matrix Chemistry.Stoichiometry

namespace PhyslibExtTest.Chemistry.Stoichiometry

/-- Methane combustion: species `[CH₄, O₂, CO₂, H₂O]`, balance rows `[C, H, O]`. -/
def methaneMatrix : Matrix (Fin 3) (Fin 4) ℤ :=
  Matrix.of ![![1, 0, 1, 0], ![4, 0, 0, 2], ![0, 2, 2, 1]]

/-- `CH₄ + 2 O₂ → CO₂ + 2 H₂O` is balanced. -/
lemma methane_isBalanced : IsBalanced methaneMatrix ![-1, -2, 1, 2] := by
  unfold IsBalanced
  decide

example : methaneMatrix *ᵥ ![0, 0, 1, 0] = ![1, 0, 2] := by
  decide

example : ¬ IsBalanced methaneMatrix ![0, 0, 1, 0] := by
  unfold IsBalanced
  decide

example {ι ρ R : Type*} [CommRing R] [Fintype ρ] (n₀ : ι → R) (ν : ρ → ι → R) :
    amountAfterExtents n₀ ν 0 = n₀ := by
  simp [amountAfterExtents]

example : amountAfterExtents (![2, 5, 0, 0] : Fin 4 → ℤ) (fun _ : Unit => ![-1, -2, 1, 2])
    (fun _ => 2) = ![0, 1, 2, 4] := by
  decide

example : methaneMatrix *ᵥ amountAfterExtents ![2, 5, 0, 0] (fun _ : Unit => ![-1, -2, 1, 2])
    (fun _ => 2) = methaneMatrix *ᵥ ![2, 5, 0, 0] :=
  mulVec_amountAfterExtents_of_isBalanced _ _ _ _ fun _ => methane_isBalanced

example : methaneMatrix *ᵥ (![2, 5, 0, 0] + (2 : ℤ) • ![-1, -2, 1, 2]) =
    methaneMatrix *ᵥ ![2, 5, 0, 0] :=
  mulVec_add_smul_of_isBalanced _ _ _ _ methane_isBalanced

/-- Staged combustion: species `[CH₄, O₂, CO₂, H₂O, CO]`, balance rows `[C, H, O]`. -/
def stagedMatrix : Matrix (Fin 3) (Fin 5) ℤ :=
  Matrix.of ![![1, 0, 1, 0, 1], ![4, 0, 0, 2, 0], ![0, 2, 2, 1, 1]]

/-- `2 CH₄ + 3 O₂ → 2 CO + 4 H₂O` and `2 CO + O₂ → 2 CO₂`. -/
def stagedReactions : Fin 2 → Fin 5 → ℤ := ![![-2, -3, 0, 4, 2], ![0, -1, 2, 0, -2]]

lemma stagedReactions_isBalanced : ∀ r, IsBalanced stagedMatrix (stagedReactions r) := by
  unfold IsBalanced
  decide

example : amountAfterExtents ![2, 5, 0, 0, 0] stagedReactions ![1, 1] = ![0, 1, 2, 4, 0] := by
  decide

example : stagedMatrix *ᵥ amountAfterExtents ![2, 5, 0, 0, 0] stagedReactions ![1, 1] =
    stagedMatrix *ᵥ ![2, 5, 0, 0, 0] :=
  mulVec_amountAfterExtents_of_isBalanced _ _ _ _ stagedReactions_isBalanced

example : methaneMatrix.map (Int.cast : ℤ → ℚ) *ᵥ amountAfterExtents ![2, 5, 0, 0]
    (fun (_ : Unit) (s : Fin 4) => ((![-1, -2, 1, 2] : Fin 4 → ℤ) s : ℚ)) (fun _ => 1 / 2) =
    methaneMatrix.map (Int.cast : ℤ → ℚ) *ᵥ ![2, 5, 0, 0] :=
  mulVec_amountAfterExtents_of_isBalanced _ _ _ _ fun _ => methane_isBalanced.intCast

/-- Iron reduction: species `[Fe³⁺, e⁻, Fe²⁺]`, balance rows `[Fe, charge]`. -/
def ironMatrix : Matrix (Fin 2) (Fin 3) ℤ :=
  Matrix.of ![![1, 0, 1], ![3, -1, 2]]

example : IsBalanced ironMatrix ![-1, -1, 1] := by
  unfold IsBalanced
  decide

example : ¬ IsBalanced ironMatrix ![-1, 0, 1] := by
  unfold IsBalanced
  decide

end PhyslibExtTest.Chemistry.Stoichiometry

#print axioms Chemistry.Stoichiometry.mulVec_amountAfterExtents_of_isBalanced
#print axioms Chemistry.Stoichiometry.mulVec_add_smul_of_isBalanced
#print axioms Chemistry.Stoichiometry.IsBalanced.intCast
