/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual original-presentation word values of the finite C322 representative candidates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexRepresentatives
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportProgram
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationFiniteEquationSources
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationRawInstructionEquality

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each finite representative denotes its exact acyclic original source word. -/
noncomputable def y322TCIndexRepresentative (i : Fin 3159) : Y322Presentation :=
  y322LocalProgramValue y322TransportProgram
    ⟨38540 + (y322TCIndexRepresentativeNode i).val, by omega⟩

/-- The literal numbered representative word, with the empty base representative separated. -/
def y322TCIndexRepresentativeWord (i : Fin 3159) : List (Fin 48648 × Bool) :=
  if (y322TCIndexRepresentativeNode i).val = 0 then []
  else [(⟨38548 + (y322TCIndexRepresentativeNode i).val, by omega⟩, true)]

/-- The original base transversal instruction is exactly the empty word instruction. -/
theorem y322TCIndexBase_instruction : y322TransportProgram 38540 = .one := by
  decide +kernel

/-- Its acyclic original source value is therefore one. -/
theorem y322TCIndexBase_value : y322LocalProgramValue y322TransportProgram 38540 = 1 := by
  rw [y322LocalProgramValue_eq, y322TCIndexBase_instruction]
  rfl

/-- The finite base candidate has the original trace-node label zero. -/
theorem y322TCIndexRepresentativeNode_zero : y322TCIndexRepresentativeNode 0 = 0 := by
  decide +kernel

/-- The actual base candidate is one in the original C322 group. -/
theorem y322TCIndexRepresentative_zero : y322TCIndexRepresentative 0 = 1 := by
  unfold y322TCIndexRepresentative
  have he : (⟨38540 + (y322TCIndexRepresentativeNode 0).val, by omega⟩ : Fin 48640) =
      38540 := by
    apply Fin.ext
    simp [y322TCIndexRepresentativeNode_zero]
  rw [he]
  exact y322TCIndexBase_value

/-- Every literal numbered representative word has its declared actual source-group value. -/
theorem y322TCIndexRepresentativeWord_value (i : Fin 3159) :
    y322EquationWordValue (y322FiniteAuxiliaryValue y322TransportProgram)
      (y322TCIndexRepresentativeWord i) = y322TCIndexRepresentative i := by
  unfold y322TCIndexRepresentativeWord
  split
  · rename_i h
    unfold y322TCIndexRepresentative
    simp only [h, Nat.add_zero]
    exact y322TCIndexBase_value.symm
  · unfold y322EquationWordValue
    rw [FreeGroup.lift_mk]
    simp only [List.map_cons, List.map_nil, Bool.cond_true, List.prod_cons, List.prod_nil, mul_one]
    let ref : Fin 48640 := ⟨38540 + (y322TCIndexRepresentativeNode i).val, by omega⟩
    have he : finSumFinEquiv (Sum.inr ref : Fin 8 ⊕ Fin 48640) =
        (⟨38548 + (y322TCIndexRepresentativeNode i).val, by omega⟩ : Fin 48648) := by
      apply Fin.ext
      dsimp [ref, finSumFinEquiv]
      omega
    rw [← he]
    exact y322FiniteAuxiliaryValue_number y322TransportProgram (.inr ref)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
