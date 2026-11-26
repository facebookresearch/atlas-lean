/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ConstructibleComplexesLocalSystemCokernel

/-!
# Tests for cokernels of finite-rank local systems

The theorem applies to maps between constant rational sheaves and to
iterated cokernels of finite-rank local systems.
Sources: Dimca, *Sheaves in Topology*, Chapters 2–4; de Cataldo–Migliorini,
https://arxiv.org/abs/0712.0349, §1.5.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.ConstructibleComplexesLocalSystemCokernel

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open MathlibExt.AlgebraicGeometry.ConstructibleComplexes
open WantedExt.AlgebraicGeometry.ConstructibleComplexesWanted

example (Z : TopCat.{0})
    (a : (constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ) ⟶
      (constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} ℚ)).obj
        (ModuleCat.of ℚ (Fin 2 → ℚ))) :
    IsFiniteRankLocalSystem ℚ Z (cokernel a) :=
  localSystem_cokernel ℚ Z _ _ a
    (isFiniteRankLocalSystem_constantSheaf ℚ Z (ModuleCat.of ℚ ℚ))
    (isFiniteRankLocalSystem_constantSheaf ℚ Z (ModuleCat.of ℚ (Fin 2 → ℚ)))

example (k : Type) [Field k] (Z : TopCat.{0}) (F G : CoefficientSheaf k Z)
    (a : F ⟶ G) (hF : IsFiniteRankLocalSystem k Z F)
    (hG : IsFiniteRankLocalSystem k Z G) :
    IsFiniteRankLocalSystem k Z (cokernel (cokernel.π a)) :=
  localSystem_cokernel k Z G (cokernel a) (cokernel.π a) hG
    (localSystem_cokernel k Z F G a hF hG)

end MathlibExtTest.AlgebraicGeometry.ConstructibleComplexesLocalSystemCokernel
