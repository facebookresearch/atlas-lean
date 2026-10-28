/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Original sources and previously proved local equations for the full transversal edge proof. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCContextRecognition

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Original local relators and acyclic definitions, then already proved literal equations. -/
def y322TCIndexSource (i : Fin 77243) : Y322WordEquation (Fin 48648) :=
  if h : i.val < 48713 then y322FiniteEquationSource y322TransportProgram ⟨i.val, h⟩
  else (y322TCContextProgram ⟨i.val - 48713, by omega⟩).1

/-- All edge-derivation sources hold in the original C322 group without a recognition assumption. -/
theorem y322TCIndexSource_valid (i : Fin 77243) :
    (y322TCIndexSource i).Valid (y322FiniteAuxiliaryValue y322TransportProgram) := by
  unfold y322TCIndexSource
  split
  · exact y322FiniteEquationSource_valid y322TransportProgram _
  · exact y322TCContextProgram_valid _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
