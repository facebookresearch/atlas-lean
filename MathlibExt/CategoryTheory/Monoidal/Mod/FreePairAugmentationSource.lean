/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.Mod.DayEvaluation
import MathlibExt.CategoryTheory.Monoidal.Mod.FreePairAugmentation

/-!
# Full coefficient sources of the original free-pair augmentation

The complete original source maps, carrier unit and counit, and coefficient
arrows are retained throughout the displayed identities.
-/

set_option autoImplicit false
noncomputable section
universe u v uD vD
open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.MonObj
namespace CategoryTheory.Mod.FreePairAugmentation
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (A : CommMon C) [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
/-- The original relative module tensor in the free-pair source equations. -/
local instance originalModuleMonoidal : MonoidalCategory (Mod C A.X) := Mod.instMonoidalCategory A

/-- Every full original coefficient pre-map passes through both actual free generators. -/
theorem tensor_left_unit_generator_precompose (R P Q : C) (N : Mod C A.X)
    (h : R ⟶ P ⊗ Q) (f : (Mod.free A.X).obj P ⟶ Mod.regular A.X)
    (g : (Mod.free A.X).obj Q ⟶ N) :
    Mod.FreeRelativeTensor.freeUnit A R ≫
        ((Mod.free A.X).map h ≫ (Mod.FreePairRelativeTensor.iso A P Q).inv ≫
          (f ⊗ₘ g) ≫ (λ_ N).hom).hom =
      h ≫ ((Mod.FreeRelativeTensor.freeUnit A P ≫ f.hom) ⊗ₘ
        (Mod.FreeRelativeTensor.freeUnit A Q ≫ g.hom)) ≫ N.mod.smul := by
  have hn : Mod.FreeRelativeTensor.freeUnit A R ≫ ((Mod.free A.X).map h).hom =
      h ≫ Mod.FreeRelativeTensor.freeUnit A (P ⊗ Q) :=
    ((Mod.freeForgetAdjunction A.X).unit.naturality h).symm
  simp only [Mod.comp_hom']
  rw [← Category.assoc (Mod.FreeRelativeTensor.freeUnit A R) ((Mod.free A.X).map h).hom, hn]
  simp only [Category.assoc]
  have hg := tensor_left_unit_generator A P Q N f g
  simpa only [Mod.comp_hom', Category.assoc] using congrArg (fun z => h ≫ z) hg

/-- The actual full Hom correspondence retains that coefficient and both original free generators. -/
theorem tensor_left_unit_homEquiv_precompose (R P Q : C) (N : Mod C A.X)
    (h : R ⟶ P ⊗ Q) (f : (Mod.free A.X).obj P ⟶ Mod.regular A.X)
    (g : (Mod.free A.X).obj Q ⟶ N) :
    (Mod.freeForgetAdjunction A.X).homEquiv R N
        ((Mod.free A.X).map h ≫ (Mod.FreePairRelativeTensor.iso A P Q).inv ≫
          (f ⊗ₘ g) ≫ (λ_ N).hom) =
      h ≫ ((Mod.FreeRelativeTensor.freeUnit A P ≫ f.hom) ⊗ₘ
        (Mod.FreeRelativeTensor.freeUnit A Q ≫ g.hom)) ≫ N.mod.smul := by
  rw [Adjunction.homEquiv_unit]
  exact tensor_left_unit_generator_precompose A R P Q N h f g

variable {D : Type uD} [Category.{vD} D]

/-- Every original projection retains the full coefficient/source arrow and
both actual free generators before the complete target module action. -/
theorem tensor_left_unit_generator_projection (E : C ⥤ D) (R P Q : C)
    (N : Mod C A.X) (h : R ⟶ P ⊗ Q)
    (f : (Mod.free A.X).obj P ⟶ Mod.regular A.X)
    (g : (Mod.free A.X).obj Q ⟶ N) :
    E.map (Mod.FreeRelativeTensor.freeUnit A R) ≫
      E.map ((Mod.free A.X).map h ≫ (Mod.FreePairRelativeTensor.iso A P Q).inv ≫
        (f ⊗ₘ g) ≫ (λ_ N).hom).hom =
      E.map h ≫ E.map (((Mod.FreeRelativeTensor.freeUnit A P ≫ f.hom) ⊗ₘ
        (Mod.FreeRelativeTensor.freeUnit A Q ≫ g.hom)) ≫ N.mod.smul) := by
  have hs := tensor_left_unit_generator_precompose A R P Q N h f g
  simpa only [Functor.map_comp] using congrArg E.map hs


end CategoryTheory.Mod.FreePairAugmentation

universe uI vI uV vV
namespace CategoryTheory.Mod.FreePairAugmentation
variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [MonoidalCategory (DayFunctor I V)] [BraidedCategory (DayFunctor I V)]
  [HasCoequalizers (DayFunctor I V)]
  [∀ X : DayFunctor I V, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : DayFunctor I V, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (A : CommMon (DayFunctor I V))
/-- The original relative Day-module tensor in the source component equation. -/
local instance originalDayModuleMonoidal : MonoidalCategory (Mod (DayFunctor I V) A.X) :=
  Mod.instMonoidalCategory A

/-- The actual coefficient projection retains the full original source
pre-map, both free generators and the whole original target action. -/
theorem tensor_left_unit_generator_component (R P Q : DayFunctor I V)
    (N : Mod (DayFunctor I V) A.X) (h : R ⟶ P ⊗ Q)
    (f : (Mod.free A.X).obj P ⟶ Mod.regular A.X)
    (g : (Mod.free A.X).obj Q ⟶ N) (q : I) :
    (Mod.FreeRelativeTensor.freeUnit A R).natTrans.app q ≫
      ((Mod.free A.X).map h ≫ (Mod.FreePairRelativeTensor.iso A P Q).inv ≫
        (f ⊗ₘ g) ≫ (λ_ N).hom).hom.natTrans.app q =
      h.natTrans.app q ≫
        (((Mod.FreeRelativeTensor.freeUnit A P ≫ f.hom) ⊗ₘ
          (Mod.FreeRelativeTensor.freeUnit A Q ≫ g.hom)) ≫ N.mod.smul).natTrans.app q := by
  have hs := tensor_left_unit_generator_precompose A R P Q N h f g
  have hp := congrArg (fun z => z.natTrans.app q) hs
  simpa only [DayFunctor.comp_natTrans, NatTrans.comp_app] using hp

end CategoryTheory.Mod.FreePairAugmentation
