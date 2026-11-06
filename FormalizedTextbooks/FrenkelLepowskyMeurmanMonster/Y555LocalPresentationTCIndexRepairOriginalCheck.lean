/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original instruction soundness and exact checks outside the replacement indices. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexRepairSelection

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original instructions are checked where the replacement selector leaves them in use. -/
def y322TCIndexUnreplacedCheckAt (index : ℕ) : Prop :=
  if h : index < 174819 then
    y322TCIndexRepairLookup ⟨index, h⟩ = none → y322TCIndexCheckAt index
  else True

/-- The exact original-instruction predicate outside replacement indices is decidable. -/
instance y322TCIndexUnreplacedCheckAtDecidable (index : ℕ) :
    Decidable (y322TCIndexUnreplacedCheckAt index) := by
  unfold y322TCIndexUnreplacedCheckAt
  split <;> infer_instance

/-- One unchanged checked instruction holds whenever its earlier actual equations hold. -/
theorem y322TCIndexOriginalChecked_valid (i : Fin 174819)
    (hc : y322TCIndexCheckAt i.val)
    (hp : ∀ j : Fin 174819, j.val < i.val →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram i).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram) := by
  have hi : y322ContextEquationProgramChecked y322TCIndexSource y322TCIndexProgram i := by
    simpa only [y322TCIndexCheckAt, dite_eq_left i.isLt] using hc
  cases hd : (y322TCIndexProgram i).2 with
  | inl s =>
    simp only [y322ContextEquationProgramChecked, hd, y322EquationsSameReduction] at hi
    exact y322WordEquation_transport _ _ _ (y322TCIndexSource_valid s) hi.1 hi.2
  | inr moves =>
    simp only [y322ContextEquationProgramChecked, hd] at hi
    exact y322ContextEquationRun_valid _ _
      (fun a => hp (y322ProgramPrior i a) a.isLt) moves _ _ hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
