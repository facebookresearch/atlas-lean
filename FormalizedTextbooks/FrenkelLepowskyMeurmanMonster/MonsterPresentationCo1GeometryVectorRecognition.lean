/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The full original-line finite replay identifies the actual Conway source universal module. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorSpan
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryVectorLinearComparison
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryUniversalEquivariance
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

set_option maxRecDepth 16000 in
set_option maxHeartbeats 24000000 in
-- Unfold only the twenty-four actual basis entries of the finite point registry.
/-- The candidate source basis retains the original literal actual lattice words. -/
theorem monsterCo1GeometryVectorBasisPoint_actual_word (j : Fin 24) :
    monsterCo1GeometryVectorBasisPoint j =
      (QuotientGroup.mk (omegaOrbitWordIsometry (omegaOrbitWords j)) : Co1) •
        monsterCo1GeometryBasePoint := by
  fin_cases j <;> rfl

/-- Each natural source basis image is the original independently checked actual orbit column. -/
theorem monsterCo1GeometryVectorBasisValue_image (j : Fin 24) :
    monsterCo1GeometryUniversalBinary (monsterCo1GeometryVectorBasisValue j) =
      fun i => omegaOrbitColumns i j := by
  rw [monsterCo1GeometryVectorBasisValue, monsterCo1GeometryUniversalBinary_point,
    monsterCo1GeometryVectorBasisPoint_actual_word]
  change leechBinaryAction (omegaOrbitWordIsometry (omegaOrbitWords j))
    monsterCo1GeometryBasePoint.val = _
  rw [monsterCo1GeometryBasePoint_binary, ← omegaOrbitWord_binary,
    omegaOrbit_words_certificate]

/-- The natural map of the independently defined genuine-line universal source module has
trivial kernel, by the full original-source replay and actual image inverse certificate. -/
theorem monsterCo1GeometryUniversalBinary_injective :
    Function.Injective monsterCo1GeometryUniversalBinary := by
  apply monsterCo1GeometryVector_natural_injective monsterCo1GeometryVectorBasisValue
    monsterCo1GeometryUniversalBinary omegaOrbitColumns omegaOrbitColumnsInverse
  · exact monsterCo1GeometryVectorBasisSpan_eq_top
  · exact monsterCo1GeometryVectorBasisValue_image
  · decide +kernel

/-- The original source universal module is naturally the actual twenty-four-dimensional module. -/
def monsterCo1GeometryUniversalBinaryEquiv :
    MonsterCo1GeometryUniversalModule ≃ₗ[ZMod 2] (Fin 24 → ZMod 2) :=
  LinearEquiv.ofBijective monsterCo1GeometryUniversalBinary
    ⟨monsterCo1GeometryUniversalBinary_injective, monsterCo1GeometryUniversalBinary_surjective⟩

/-- The recognition equivalence preserves every original source point generator. -/
theorem monsterCo1GeometryUniversalBinaryEquiv_point (p : MonsterCo1GeometryPoint) :
    monsterCo1GeometryUniversalBinaryEquiv (monsterCo1GeometryUniversalPoint p) = p.val :=
  monsterCo1GeometryUniversalBinary_point p

/-- The natural recognition equivalence intertwines the exact existing Conway action. -/
theorem monsterCo1GeometryUniversalBinaryEquiv_action (g : Co1)
    (v : MonsterCo1GeometryUniversalModule) :
    monsterCo1GeometryUniversalBinaryEquiv (monsterCo1GeometryUniversalAction g v) =
      co1BinaryAction g (monsterCo1GeometryUniversalBinaryEquiv v) :=
  monsterCo1GeometryUniversalBinary_action g v

/-- The genuine-line universal source module has exact dimension twenty-four. -/
theorem monsterCo1GeometryUniversalModule_finrank :
    Module.finrank (ZMod 2) MonsterCo1GeometryUniversalModule = 24 := by
  simpa only [Module.finrank_fin_fun] using monsterCo1GeometryUniversalBinaryEquiv.finrank_eq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
