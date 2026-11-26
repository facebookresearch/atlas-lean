/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ConstructibleComplexesLocalSystemKernel

/-!
# Tests for kernels of finite-rank local systems

The kernel theorem applies to the constant projection from two rational coordinates
on `ℝ`, and to arbitrary morphisms between constant sheaves of ranks three and two
on `ℝ ⊕ ℝ`.

Sources: Dimca, *Sheaves in Topology*, Chapters 2–4; de Cataldo–Migliorini,
https://arxiv.org/abs/0712.0349, §1.5.
-/

@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.ConstructibleComplexesLocalSystemKernel

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open MathlibExt.AlgebraicGeometry.ConstructibleComplexes
open WantedExt.AlgebraicGeometry.ConstructibleComplexesWanted

example : IsFiniteRankLocalSystem ℚ (TopCat.of ℝ)
    (kernel ((constantSheaf (Opens.grothendieckTopology ℝ) (ModuleCat.{0} ℚ)).map
      (ModuleCat.ofHom (LinearMap.fst ℚ ℚ ℚ)))) := by
  apply localSystem_kernel
  · exact isFiniteRankLocalSystem_constantSheaf ℚ (TopCat.of ℝ) (ModuleCat.of ℚ (ℚ × ℚ))
  · exact isFiniteRankLocalSystem_constantSheaf ℚ (TopCat.of ℝ) (ModuleCat.of ℚ ℚ)

example (a : (constantSheaf (Opens.grothendieckTopology (ℝ ⊕ ℝ)) (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ (Fin 3 → ℚ)) ⟶
      (constantSheaf (Opens.grothendieckTopology (ℝ ⊕ ℝ)) (ModuleCat.{0} ℚ)).obj
        (ModuleCat.of ℚ (Fin 2 → ℚ))) :
    IsFiniteRankLocalSystem ℚ (TopCat.of (ℝ ⊕ ℝ)) (kernel a) := by
  apply localSystem_kernel
  · exact isFiniteRankLocalSystem_constantSheaf ℚ (TopCat.of (ℝ ⊕ ℝ))
      (ModuleCat.of ℚ (Fin 3 → ℚ))
  · exact isFiniteRankLocalSystem_constantSheaf ℚ (TopCat.of (ℝ ⊕ ℝ))
      (ModuleCat.of ℚ (Fin 2 → ℚ))

end MathlibExtTest.AlgebraicGeometry.ConstructibleComplexesLocalSystemKernel
