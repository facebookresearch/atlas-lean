/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Monoidal.RightModuleRelativeTensor

/-!
# Whole projection laws for the stock transported right-module coherence

The selected associator and unitors use the original conversion's unit and
counit between the iterated Mod relative tensors. Every projection is the
original chosen coequalizer projection.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory MonObj MonoidalOpposite
open CategoryTheory.CommutativeModuleConversion
open CategoryTheory.CommutativeModuleConversion.RightModule
open scoped CategoryTheory.MonObj

namespace CategoryTheory.RightModuleFree

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction
variable (M : C) [MonObj M] [SymmetricCategory C] [IsCommMonObj M]
variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The monoidal structure on `Mod C M` given by the scalar commutative monoid of `M`, as a
local instance. -/
local instance : MonoidalCategory (Mod C M) := Mod.instMonoidalCategory (scalarCommMon M)
/-- The transported tensor product `tensorMonoidal M` on right modules, as a local instance. -/
local instance : MonoidalCategory (RightModule M) := tensorMonoidal M
/-- The transported symmetric structure `tensorSymmetric M` on right modules, as a local
instance. -/
local instance : SymmetricCategory (RightModule M) := tensorSymmetric M

/-- The actual right whisker has the original full projection value. -/
@[reassoc]
theorem relativeTensorWhiskerRight_π {X X' : RightModule M}
    (f : X ⟶ X') (Y : RightModule M) :
    relativeTensorπ M X Y ≫ (f ▷ Y).hom =
      (f.hom ▷ Y.X) ≫ relativeTensorπ M X' Y := by
  simpa only [relativeTensorMap, Mod.id_hom', tensorHom_id] using
    relativeTensorMap_π M f (𝟙 Y)

/-- The actual left whisker has the original full projection value. -/
@[reassoc]
theorem relativeTensorWhiskerLeft_π (X : RightModule M)
    {Y Y' : RightModule M} (f : Y ⟶ Y') :
    relativeTensorπ M X Y ≫ (X ◁ f).hom =
      (X.X ◁ f.hom) ≫ relativeTensorπ M X Y' := by
  simpa only [relativeTensorMap, Mod.id_hom', id_tensorHom] using
    relativeTensorMap_π M (𝟙 X) f

/-- The actual selected left-module right whisker has its complete projection value. -/
@[reassoc]
theorem leftModuleRelativeTensorWhiskerRight_π {X X' : Mod C M}
    (f : X ⟶ X') (Y : Mod C M) :
    Mod.relativeTensorπ (scalarCommMon M) X Y ≫ (f ▷ Y).hom =
      (f.hom ▷ Y.X) ≫ Mod.relativeTensorπ (scalarCommMon M) X' Y := by
  have h := Mod.relativeTensorMap_π (scalarCommMon M) f (𝟙 Y)
  change Mod.relativeTensorπ (scalarCommMon M) X Y ≫ (f ⊗ₘ (𝟙 Y)).hom =
    (f.hom ⊗ₘ (𝟙 Y.X)) ≫ Mod.relativeTensorπ (scalarCommMon M) X' Y at h
  rw [tensorHom_id, tensorHom_id] at h
  exact h

/-- The actual selected left-module left whisker has its complete projection value. -/
@[reassoc]
theorem leftModuleRelativeTensorWhiskerLeft_π (X : Mod C M)
    {Y Y' : Mod C M} (f : Y ⟶ Y') :
    Mod.relativeTensorπ (scalarCommMon M) X Y ≫ (X ◁ f).hom =
      (X.X ◁ f.hom) ≫ Mod.relativeTensorπ (scalarCommMon M) X Y' := by
  have h := Mod.relativeTensorMap_π (scalarCommMon M) (𝟙 X) f
  change Mod.relativeTensorπ (scalarCommMon M) X Y ≫ ((𝟙 X) ⊗ₘ f).hom =
    ((𝟙 X.X) ⊗ₘ f.hom) ≫ Mod.relativeTensorπ (scalarCommMon M) X Y' at h
  rw [id_tensorHom, id_tensorHom] at h
  exact h

/-- The selected associator retains both actual left-module recovery isomorphisms. -/
@[reassoc]
theorem relativeTensorAssociator_hom_π (X Y Z : RightModule M) :
    (relativeTensorπ M X Y ▷ Z.X) ≫
        relativeTensorπ M (X ⊗ Y) Z ≫ (α_ X Y Z).hom.hom =
      (α_ X.X Y.X Z.X).hom ≫ (X.X ◁ relativeTensorπ M Y Z) ≫
        relativeTensorπ M X (Y ⊗ Z) := by
  let L := CommutativeModuleConversion.moduleEquivalence M
  let LX := L.inverse.obj X
  let LY := L.inverse.obj Y
  let LZ := L.inverse.obj Z
  let XY := LX ⊗ LY
  let YZ := LY ⊗ LZ
  let uXY := L.unitIso.app XY
  let uYZ := L.unitIso.app YZ
  have hl :
      Mod.relativeTensorπ (scalarCommMon M) (L.inverse.obj (L.functor.obj XY)) LZ ≫
          (uXY.inv ▷ LZ).hom =
        (uXY.inv.hom ▷ LZ.X) ≫ Mod.relativeTensorπ (scalarCommMon M) XY LZ := by
    exact leftModuleRelativeTensorWhiskerRight_π M uXY.inv LZ
  have hr :
      Mod.relativeTensorπ (scalarCommMon M) LX YZ ≫ (LX ◁ uYZ.hom).hom =
        (LX.X ◁ uYZ.hom.hom) ≫
          Mod.relativeTensorπ (scalarCommMon M) LX (L.inverse.obj (L.functor.obj YZ)) := by
    exact leftModuleRelativeTensorWhiskerLeft_π M LX uYZ.hom
  have huXY : uXY.inv.hom = 𝟙 XY.X :=
    CommutativeModuleConversion.leftRecoveryIso_hom M XY
  have huYZ : uYZ.hom.hom = 𝟙 YZ.X :=
    CommutativeModuleConversion.leftRecoveryIso_inv M YZ
  have hcoh : (α_ X Y Z).hom = toRightMap M
      ((uXY.inv ▷ LZ) ≫ (α_ LX LY LZ).hom ≫ (LX ◁ uYZ.hom)) := rfl
  rw [hcoh, toRightMap_hom]
  simp only [Mod.comp_hom']
  change (Mod.relativeTensorπ (scalarCommMon M) LX LY ▷ LZ.X) ≫
      Mod.relativeTensorπ (scalarCommMon M) (L.inverse.obj (L.functor.obj XY)) LZ ≫
        (uXY.inv ▷ LZ).hom ≫ (α_ LX LY LZ).hom.hom ≫ (LX ◁ uYZ.hom).hom =
    (α_ LX.X LY.X LZ.X).hom ≫ (LX.X ◁ Mod.relativeTensorπ (scalarCommMon M) LY LZ) ≫
      Mod.relativeTensorπ (scalarCommMon M) LX (L.inverse.obj (L.functor.obj YZ))
  erw [reassoc_of% hl, huXY, id_whiskerRight, Category.id_comp]
  erw [reassoc_of% (Mod.relativeTensorAssociator_hom_π
    (scalarCommMon M) LX LY LZ)]
  erw [hr, huYZ, whiskerLeft_id, Category.id_comp]

/-- The actual left unitor has the entire converted left-action characteristic. -/
@[reassoc]
theorem relativeTensorLeftUnitor_hom_π (X : RightModule M) :
    relativeTensorπ M (𝟙_ (RightModule M)) X ≫ (λ_ X).hom.hom =
      CommutativeModuleConversion.leftAction M X := by
  let L := CommutativeModuleConversion.moduleEquivalence M
  let LX := L.inverse.obj X
  let U := (𝟙_ (Mod C M))
  let u := L.unitIso.app U
  have hm :
      Mod.relativeTensorπ (scalarCommMon M) (L.inverse.obj (L.functor.obj U)) LX ≫
          (u.inv ▷ LX).hom =
        (u.inv.hom ▷ LX.X) ≫ Mod.relativeTensorπ (scalarCommMon M) U LX := by
    exact leftModuleRelativeTensorWhiskerRight_π M u.inv LX
  have hu : u.inv.hom = 𝟙 M :=
    CommutativeModuleConversion.leftRecoveryIso_hom M U
  have hc : (L.counitIso.hom.app X).hom = 𝟙 X.X :=
    CommutativeModuleConversion.rightRecoveryIso_hom M X
  have hcoh : (λ_ X).hom =
      toRightMap M ((u.inv ▷ LX) ≫ (λ_ LX).hom) ≫ L.counitIso.hom.app X := rfl
  rw [hcoh]
  dsimp only [L, LX, CommutativeModuleConversion.moduleEquivalence,
    CommutativeModuleConversion.leftToRight, CommutativeModuleConversion.rightToLeft]
  simp only [Mod.comp_hom']
  rw [toRightMap_hom]
  simp only [Mod.comp_hom']
  change Mod.relativeTensorπ (scalarCommMon M) (L.inverse.obj (L.functor.obj U)) LX ≫
      (((u.inv ▷ LX).hom ≫ (λ_ LX).hom.hom) ≫ (L.counitIso.hom.app X).hom) = LX.mod.smul
  erw [Category.assoc]
  erw [hc, Category.comp_id, reassoc_of% hm, hu, id_whiskerRight, Category.id_comp]
  exact Mod.relativeTensorLeftUnitor_hom_π (scalarCommMon M) LX

/-- The actual right unitor has the entire original right-action characteristic. -/
@[reassoc]
theorem relativeTensorRightUnitor_hom_π (X : RightModule M) :
    relativeTensorπ M X (𝟙_ (RightModule M)) ≫ (ρ_ X).hom.hom =
      ModObj.smul (M := mop M) (X := X.X) := by
  let L := CommutativeModuleConversion.moduleEquivalence M
  let LX := L.inverse.obj X
  let U := (𝟙_ (Mod C M))
  let u := L.unitIso.app U
  have hm :
      Mod.relativeTensorπ (scalarCommMon M) LX (L.inverse.obj (L.functor.obj U)) ≫
          (LX ◁ u.inv).hom =
        (LX.X ◁ u.inv.hom) ≫ Mod.relativeTensorπ (scalarCommMon M) LX U := by
    exact leftModuleRelativeTensorWhiskerLeft_π M LX u.inv
  have hu : u.inv.hom = 𝟙 M :=
    CommutativeModuleConversion.leftRecoveryIso_hom M U
  have hc : (L.counitIso.hom.app X).hom = 𝟙 X.X :=
    CommutativeModuleConversion.rightRecoveryIso_hom M X
  have hcoh : (ρ_ X).hom =
      toRightMap M ((LX ◁ u.inv) ≫ (ρ_ LX).hom) ≫ L.counitIso.hom.app X := rfl
  rw [hcoh]
  dsimp only [L, LX, CommutativeModuleConversion.moduleEquivalence,
    CommutativeModuleConversion.leftToRight, CommutativeModuleConversion.rightToLeft]
  simp only [Mod.comp_hom']
  rw [toRightMap_hom]
  simp only [Mod.comp_hom']
  change Mod.relativeTensorπ (scalarCommMon M) LX (L.inverse.obj (L.functor.obj U)) ≫
      (((LX ◁ u.inv).hom ≫ (ρ_ LX).hom.hom) ≫ (L.counitIso.hom.app X).hom) = _
  erw [Category.assoc]
  erw [hc, Category.comp_id, reassoc_of% hm, hu, whiskerLeft_id, Category.id_comp,
    Mod.relativeTensorRightUnitor_hom_π]
  change (β_ X.X M).hom ≫ (β_ M X.X).hom ≫
    ModObj.smul (M := mop M) (X := X.X) = _
  rw [SymmetricCategory.symmetry_assoc]

end CategoryTheory.RightModuleFree
