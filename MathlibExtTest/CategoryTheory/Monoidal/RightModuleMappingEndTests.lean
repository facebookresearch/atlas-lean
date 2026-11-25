/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

import MathlibExt.CategoryTheory.Monoidal.RightModuleMappingEnd
import MathlibExt.CategoryTheory.Monoidal.RightModuleMappingEndEvaluation

/-!
# Public clients of the source right-module mapping equalizer

The first section deliberately has no scalar commutativity premise. It checks
the full parameter representation, both original variances, and evaluation of
lifted families. The commutative section checks the actual source/stock action
comparison and the balanced adjunction on the unchanged right-module carrier.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory MonoidalOpposite
open CategoryTheory.CommutativeModuleConversion
open CategoryTheory.CommutativeModuleConversion.RightModule
open scoped MonoidalClosed CategoryTheory.MonObj

namespace CategoryTheory.RightModuleMappingEndTests

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [SymmetricCategory C] [MonoidalClosed C] [HasEqualizers C]
  (R : C) [MonObj R]

/-- A full compatible parameter family lifts without a commutative-scalar premise. -/
def represented {M N : RightModule R} {P : C}
    (q : RightModuleMappingEnd.Family R M N P) : P ⟶ RightModuleMappingEnd.Hom R M N :=
  RightModuleMappingEnd.lift R M N q

/-- The public representation recovers the whole original ambient map. -/
theorem represented_ι {M N : RightModule R} {P : C}
    (q : RightModuleMappingEnd.Family R M N P) :
    represented R q ≫ RightModuleMappingEnd.ι R M N = q.app :=
  RightModuleMappingEnd.lift_ι R M N q

/-- Public evaluation retains the full parameterized original component. -/
theorem represented_evaluation {M N : RightModule R} {P : C}
    (q : RightModuleMappingEnd.Family R M N P) :
    (M.X ◁ represented R q) ≫ RightModuleMappingEnd.evaluation R M N =
      MonoidalClosed.uncurry q.app :=
  RightModuleMappingEnd.lift_evaluation R M N q

/-- Changing a complete parameter before representation gives the original precomposed lift. -/
theorem parameter_before_representation {M N : RightModule R} {P Q : C}
    (f : P ⟶ Q) (q : RightModuleMappingEnd.Family R M N Q) :
    represented R (RightModuleMappingEnd.reparameterize R M N f q) =
      f ≫ represented R q :=
  RightModuleMappingEnd.lift_reparameterize R M N f q

/-- A represented map is reconstructed from its complete original family. -/
theorem map_round_trip {M N : RightModule R} {P : C}
    (f : P ⟶ RightModuleMappingEnd.Hom R M N) :
    (RightModuleMappingEnd.parameterEquiv R M N P).symm
      (RightModuleMappingEnd.parameterEquiv R M N P f) = f :=
  (RightModuleMappingEnd.parameterEquiv R M N P).left_inv f

/-- Every full source family, including its action condition, is reconstructed. -/
theorem family_round_trip {M N : RightModule R} {P : C}
    (q : RightModuleMappingEnd.Family R M N P) :
    RightModuleMappingEnd.parameterEquiv R M N P
      ((RightModuleMappingEnd.parameterEquiv R M N P).symm q) = q :=
  (RightModuleMappingEnd.parameterEquiv R M N P).right_inv q

/-- The source variance client retains the actual complete source carrier map. -/
def sourceChange {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    RightModuleMappingEnd.Hom R M N ⟶ RightModuleMappingEnd.Hom R M' N :=
  RightModuleMappingEnd.pre R f N

/-- Its ambient characteristic uses exactly the original source-module arrow. -/
theorem sourceChange_ι {M M' : RightModule R} (f : M' ⟶ M) (N : RightModule R) :
    sourceChange R f N ≫ RightModuleMappingEnd.ι R M' N =
      RightModuleMappingEnd.ι R M N ≫ (MonoidalClosed.pre f.hom).app N.X :=
  RightModuleMappingEnd.pre_ι R f N

/-- The target variance client retains the actual complete target carrier map. -/
def targetChange (M : RightModule R) {N N' : RightModule R} (f : N ⟶ N') :
    RightModuleMappingEnd.Hom R M N ⟶ RightModuleMappingEnd.Hom R M N' :=
  RightModuleMappingEnd.post R M f

/-- Its ambient characteristic uses exactly the original target-module arrow. -/
theorem targetChange_ι (M : RightModule R) {N N' : RightModule R} (f : N ⟶ N') :
    targetChange R M f ≫ RightModuleMappingEnd.ι R M N' =
      RightModuleMappingEnd.ι R M N ≫ (ihom M.X).map f.hom :=
  RightModuleMappingEnd.post_ι R M f

/-- Both public source and target clients commute on the whole noncommutative-scalar mapping
object. -/
theorem change_both {M M' N N' : RightModule R} (f : M' ⟶ M) (g : N ⟶ N') :
    sourceChange R f N ≫ targetChange R M' g =
      targetChange R M g ≫ sourceChange R f N' :=
  RightModuleMappingEnd.pre_post R f g

section Commutative

variable [IsCommMonObj R]

/-- The source equalizer itself has the actual right action, rather than just its stock image. -/
def sourceModule (M N : RightModule R) : RightModule R :=
  RightModuleMappingEnd.moduleObject R M N

/-- The public source module has the original whole equalizer carrier. -/
example (M N : RightModule R) :
    (sourceModule R M N).X = RightModuleMappingEnd.Hom R M N := rfl

/-- The public comparison is an isomorphism of the actual complete right modules. -/
def compareSource (M N : RightModule R) : sourceModule R M N ≅
    RightModuleMappingEnd.stockRightHom R M N :=
  RightModuleMappingEnd.moduleComparison R M N

/-- Its actual forward map preserves the whole original action-equalizer inclusion. -/
example (M N : RightModule R) :
    (compareSource R M N).hom.hom ≫ RightModuleMappingEnd.stockι R M N =
      RightModuleMappingEnd.ι R M N :=
  RightModuleMappingEnd.stockComparison_hom_ι R M N

/-- Its actual inverse map preserves the whole original action-equalizer inclusion. -/
example (M N : RightModule R) :
    (compareSource R M N).inv.hom ≫ RightModuleMappingEnd.ι R M N =
      RightModuleMappingEnd.stockι R M N :=
  RightModuleMappingEnd.stockComparison_inv_ι R M N

section Balanced

variable [HasCoequalizers C]

local instance : MonoidalCategory (RightModule R) := RightModuleFree.tensorMonoidal R
local instance : SymmetricCategory (RightModule R) := RightModuleFree.tensorSymmetric R

/-- The actual MMSS source-oriented balanced transpose lands in the original source equalizer. -/
def balancedTranspose (M N Z : RightModule R) (f : N ⊗ M ⟶ Z) :
    N ⟶ (RightModuleMappingEnd.functor R M).obj Z :=
  (RightModuleMappingEnd.adjunction R M).homEquiv N Z f

/-- The actual inverse transpose has the original source tensor order. -/
def balancedUntranspose (M N Z : RightModule R)
    (f : N ⟶ (RightModuleMappingEnd.functor R M).obj Z) : N ⊗ M ⟶ Z :=
  ((RightModuleMappingEnd.adjunction R M).homEquiv N Z).symm f

/-- Both complete balanced maps are recovered by the actual adjunction functions. -/
example (M N Z : RightModule R) (f : N ⊗ M ⟶ Z) :
    balancedUntranspose R M N Z (balancedTranspose R M N Z f) = f :=
  ((RightModuleMappingEnd.adjunction R M).homEquiv N Z).left_inv f

/-- Both entire maps into the actual source mapping module are recovered. -/
example (M N Z : RightModule R) (f : N ⟶ (RightModuleMappingEnd.functor R M).obj Z) :
    balancedTranspose R M N Z (balancedUntranspose R M N Z f) = f :=
  ((RightModuleMappingEnd.adjunction R M).homEquiv N Z).right_inv f

end Balanced
end Commutative

end CategoryTheory.RightModuleMappingEndTests
