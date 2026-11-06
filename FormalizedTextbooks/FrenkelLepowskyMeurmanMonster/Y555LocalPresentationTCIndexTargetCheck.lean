/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact finite target-equation bindings for the source local index certificate. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexCheck
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexCoefficients
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexRepresentativeValues

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The literal equation required for an actual representative-generator transition. -/
def y322TCIndexTransitionEquation (i : Fin 3159) (g : Fin 8) :
    Y322WordEquation (Fin 48648) :=
  ⟨y322TCIndexRepresentativeWord i ++ [(g.castAdd 48640, true)],
    y322TCIndexCoefficientWord i g ++
      y322TCIndexRepresentativeWord (y322TCIndexEdgeAt i g).target⟩

/-- Compare the exact source proof target with its literal coset-transition spelling. -/
def y322TCIndexTargetCheckAt (index : ℕ) : Prop :=
  if h : index < 25272 then
    let i : Fin 3159 := ⟨index / 8, by omega⟩
    let g : Fin 8 := ⟨index % 8, Nat.mod_lt _ (by decide)⟩
    y322EquationsSameReduction (y322TCIndexTransitionEquation i g)
      (y322TCIndexProgram (y322TCIndexEdgeAt i g).equation).1
  else True

/-- Literal transition target comparisons are decidable by exact free cancellation. -/
instance y322TCIndexTargetCheckAtDecidable (index : ℕ) :
    Decidable (y322TCIndexTargetCheckAt index) := by
  unfold y322TCIndexTargetCheckAt
  split
  · unfold y322EquationsSameReduction
    infer_instance
  · infer_instance

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
