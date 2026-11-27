/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.NativeTensorComparisons

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace MathlibExt.AlgebraicGeometry.NativeTensorComparisons

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open scoped TensorProduct

universe u

variable (X : Scheme.{u})

-- Instance inference: local isomorphisms are monoidal, and the comparisons are isomorphisms.
example : (localIso X).IsMonoidal := inferInstance

example (P Q : ModulePresheaves X) : IsIso (pairComparison X P Q) := inferInstance

example (L M N : X.Modules) : IsIso (tripleLeft X L M N) := inferInstance

example (L M N : X.Modules) : IsIso (tripleRight X L M N) := inferInstance

-- The associator is the transport of the presheaf associator along the two comparisons.
example (L M N : X.Modules) :
    (tensorAssociator X L M N).hom = inv (tripleLeft X L M N) ≫ tripleRight X L M N := by
  rw [← tripleLeft_comp_tensorAssociator_hom, IsIso.inv_hom_id_assoc]

-- On pure tensors: the class of `[a ⊗ b] ⊗ c` goes to the class of `a ⊗ [b ⊗ c]` and back.
example (L M N : X.Modules) (U : X.Opensᵒᵖ) (a : ((forgetModules X).obj L).obj U)
    (b : ((forgetModules X).obj M).obj U) (c : ((forgetModules X).obj N).obj U) :
    ((forgetModules X).map (tensorAssociator X L M N).inv).app' U
      (((forgetModules X).map (tensorAssociator X L M N).hom).app' U
        (((moduleAdjunction X).unit.app
          ((forgetModules X).obj (moduleTensor X L M) ⊗ (forgetModules X).obj N)).app' U
          (((moduleAdjunction X).unit.app
            ((forgetModules X).obj L ⊗ (forgetModules X).obj M)).app' U (a ⊗ₜ b) ⊗ₜ c))) =
      ((moduleAdjunction X).unit.app
        ((forgetModules X).obj (moduleTensor X L M) ⊗ (forgetModules X).obj N)).app' U
        (((moduleAdjunction X).unit.app
          ((forgetModules X).obj L ⊗ (forgetModules X).obj M)).app' U (a ⊗ₜ b) ⊗ₜ c) :=
  (congrArg (fun y ↦ ((forgetModules X).map (tensorAssociator X L M N).inv).app' U y)
    (tensorAssociator_hom_apply_tmul X L M N U a b c)).trans
    (tensorAssociator_inv_apply_tmul X L M N U a b c)

-- On pure tensors, the pair comparison is `[p ⊗ q] ↦ [[p] ⊗ [q]]`.
example (P Q : ModulePresheaves X) (U : X.Opensᵒᵖ) (p : P.obj U) (q : Q.obj U) :
    ((forgetModules X).map (pairComparison X P Q)).app' U
      (((moduleAdjunction X).unit.app (P ⊗ Q)).app' U (p ⊗ₜ q)) =
      ((moduleAdjunction X).unit.app
        ((forgetModules X).obj ((sheafifyModules X).obj P) ⊗
          (forgetModules X).obj ((sheafifyModules X).obj Q))).app' U
        (((moduleAdjunction X).unit.app P).app' U p ⊗ₜ
          ((moduleAdjunction X).unit.app Q).app' U q) :=
  pairComparison_apply_tmul X P Q U p q

end MathlibExt.AlgebraicGeometry.NativeTensorComparisons
