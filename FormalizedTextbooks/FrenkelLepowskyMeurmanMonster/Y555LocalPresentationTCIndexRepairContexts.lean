/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact replacement context derivations using original sources and earlier index equations. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexCheck

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Replacement contexts may use original sources or strictly earlier claimed index equations. -/
def y322TCIndexRepairPrior (i : Fin 174819) (reference : Fin (77243 + i.val)) :
    Y322WordEquation (Fin 48648) :=
  if h : reference.val < 77243 then y322TCIndexSource ⟨reference.val, h⟩
  else (y322TCIndexProgram ⟨reference.val - 77243, by omega⟩).1

/-- Decode the exact replacement context list after checking its source and chronological bounds. -/
def y322TCIndexRepairMoves (i : Fin 174819) (moves : List Y322RawContextEquationMove)
    (h : ∀ move ∈ moves, move.Allowed 48648 (77243 + i.val)) :
    List (Y322ContextEquationMove (Fin 48648) (77243 + i.val)) :=
  moves.pmap (fun move hm => y322RawContextEquationMoveDecode 48648 (77243 + i.val) move hm) h

/-- A replacement is accepted only by exact replay against the unchanged claimed equation. -/
def y322TCIndexRepairChecked (i : Fin 174819) (moves : List Y322RawContextEquationMove)
    (h : ∀ move ∈ moves, move.Allowed 48648 (77243 + i.val)) : Prop :=
  y322ContextEquationRun (y322TCIndexRepairPrior i) (y322TCIndexRepairMoves i moves h)
    (y322TCIndexProgram i).1.left = some (y322TCIndexProgram i).1.right

/-- Exact finite replacement replay is decidable. -/
instance y322TCIndexRepairCheckedDecidable (i : Fin 174819)
    (moves : List Y322RawContextEquationMove)
    (h : ∀ move ∈ moves, move.Allowed 48648 (77243 + i.val)) :
    Decidable (y322TCIndexRepairChecked i moves h) := by
  unfold y322TCIndexRepairChecked
  infer_instance

/-- A checked replacement follows from original sources and earlier valid equations. -/
theorem y322TCIndexRepair_valid (i : Fin 174819) (moves : List Y322RawContextEquationMove)
    (hm : ∀ move ∈ moves, move.Allowed 48648 (77243 + i.val))
    (hc : y322TCIndexRepairChecked i moves hm)
    (hp : ∀ j : Fin 174819, j.val < i.val →
      (y322TCIndexProgram j).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram)) :
    (y322TCIndexProgram i).1.Valid (y322FiniteAuxiliaryValue y322TransportProgram) := by
  apply y322ContextEquationRun_valid _ (y322TCIndexRepairPrior i) _ _ _ _ hc
  intro reference
  unfold y322TCIndexRepairPrior
  split
  · exact y322TCIndexSource_valid _
  · apply hp
    change reference.val - 77243 < i.val
    omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
