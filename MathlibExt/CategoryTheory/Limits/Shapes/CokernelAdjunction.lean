/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Cokernel adjunction — `coker ⊣ zeroToFunctor` via `π` and `cokernelZeroIsoTarget`.
-/

@[expose] public section
open CategoryTheory Category Limits
namespace CategoryTheory
namespace Arrow
universe v u
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
open ZeroObject
/-- The functor sending `X` to the arrow `0 ⟶ X` from the zero object. -/
noncomputable def zeroToFunctor : C ⥤ Arrow C where
  obj X := Arrow.mk (0 : (0 : C) ⟶ X)
  map {X Y} f := Arrow.homMk (𝟙 (0 : C)) f (HasZeroObject.from_zero_ext _ _)
  map_id X := by
    apply hom_ext
    · exact HasZeroObject.from_zero_ext _ _
    · rfl
  map_comp {X Y Z} f g := by
    apply hom_ext
    · exact HasZeroObject.from_zero_ext _ _
    · rfl

@[simp]
lemma zeroToFunctor_obj_hom (X : C) :
    (zeroToFunctor (C := C).obj X).hom = 0 := rfl

@[simp]
lemma zeroToFunctor_map_left {X Y : C} (f : X ⟶ Y) :
    (zeroToFunctor (C := C).map f).left = 𝟙 (0 : C) := rfl

@[simp]
lemma zeroToFunctor_map_right {X Y : C} (f : X ⟶ Y) :
    (zeroToFunctor (C := C).map f).right = f := rfl

end Arrow
namespace Limits
universe v₁ u₁
variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C] [HasCokernels C]
open ZeroObject
/-- Unit for `coker ⊣ zeroToFunctor`: `f → (0 ⟶ coker f)` via the cokernel projection. -/
noncomputable def cokerUnit : 𝟭 (Arrow C) ⟶ coker (C := C) ⋙ Arrow.zeroToFunctor where
  app f :=
    { left := 0
      right := cokernel.π f.hom
      w := by
        calc (0 : f.left ⟶ (0 : C)) ≫ 0 = 0 := by simp
          _ = f.hom ≫ cokernel.π f.hom := (cokernel.condition f.hom).symm }
  naturality f g φ := by
    apply Arrow.hom_ext
    · exact HasZeroObject.to_zero_ext _ _
    · exact (cokernel.π_desc f.hom (φ.right ≫ cokernel.π g.hom)
        (by simp [← Arrow.w_assoc φ])).symm

/-- Counit for `coker ⊣ zeroToFunctor` via `cokernelZeroIsoTarget.hom`. -/
noncomputable def cokerCounit : Arrow.zeroToFunctor ⋙ coker (C := C) ⟶ 𝟭 C where
  app X := (cokernelZeroIsoTarget (X := (0 : C)) (Y := X)).hom
  naturality X Y f := by
    let πX := cokernel.π (0 : (0 : C) ⟶ X)
    let πY := cokernel.π (0 : (0 : C) ⟶ Y)
    let m := (coker (C := C)).map (Arrow.zeroToFunctor.map f)
    let eX : cokernel (0 : (0 : C) ⟶ X) ⟶ X := cokernelZeroIsoTarget.hom
    let eY : cokernel (0 : (0 : C) ⟶ Y) ⟶ Y := cokernelZeroIsoTarget.hom
    have hπ : πX ≫ m = f ≫ πY := by
      have h1 : πX ≫ m = (Arrow.zeroToFunctor.map f).right ≫ πY :=
        cokernel.π_desc _ _ (HasZeroObject.from_zero_ext _ _)
      exact h1.trans rfl
    have hY : πY ≫ eY = 𝟙 Y := by
      dsimp only [eY]
      rw [cokernelZeroIsoTarget_hom]
      exact cokernel.π_desc _ _ _
    have hX : πX ≫ eX = 𝟙 X := by
      dsimp only [eX]
      rw [cokernelZeroIsoTarget_hom]
      exact cokernel.π_desc _ _ _
    apply (cancel_epi πX).mp
    have h1 : πX ≫ (m ≫ eY) = f := by
      have ha : πX ≫ (m ≫ eY) = (πX ≫ m) ≫ eY := (Category.assoc πX m eY).symm
      have hb : (πX ≫ m) ≫ eY = (f ≫ πY) ≫ eY := congrArg (· ≫ eY) hπ
      have hc : (f ≫ πY) ≫ eY = f ≫ (πY ≫ eY) := Category.assoc f πY eY
      have hd : f ≫ (πY ≫ eY) = f ≫ 𝟙 Y := congrArg (f ≫ ·) hY
      exact ha.trans (hb.trans (hc.trans (hd.trans (by simp))))
    have h2 : πX ≫ (eX ≫ f) = f := by
      have ha : πX ≫ (eX ≫ f) = (πX ≫ eX) ≫ f := (Category.assoc πX eX f).symm
      have hb : (πX ≫ eX) ≫ f = 𝟙 X ≫ f := congrArg (· ≫ f) hX
      exact ha.trans (hb.trans (by simp))
    exact h1.trans h2.symm

/-- `Limits.coker` is left adjoint to `Arrow.zeroToFunctor`. -/
noncomputable def cokerAdjunction : coker (C := C) ⊣ Arrow.zeroToFunctor where
  unit := cokerUnit
  counit := cokerCounit
  left_triangle_components f := by
    let πf := cokernel.π f.hom
    let π0 := cokernel.π (0 : (0 : C) ⟶ cokernel f.hom)
    let m := (coker (C := C)).map ((cokerUnit (C := C)).app f)
    let e : cokernel (0 : (0 : C) ⟶ cokernel f.hom) ⟶ cokernel f.hom :=
      cokernelZeroIsoTarget.hom
    let u : f.right ⟶ cokernel f.hom := ((cokerUnit (C := C)).app f).right
    have hm : πf ≫ m = πf ≫ π0 := by
      have h1 : πf ≫ m = u ≫ π0 := by
        have hcond : f.hom ≫ (u ≫ π0) = 0 := by
          calc f.hom ≫ (u ≫ π0)
              = (f.hom ≫ u) ≫ π0 := by rw [← Category.assoc]
            _ = (f.hom ≫ πf) ≫ π0 := rfl
            _ = 0 ≫ π0 := by rw [cokernel.condition]
            _ = 0 := by rw [zero_comp]
        exact cokernel.π_desc f.hom _ hcond
      exact h1.trans rfl
    have he : π0 ≫ e = 𝟙 _ := by
      dsimp only [e]
      rw [cokernelZeroIsoTarget_hom]
      exact cokernel.π_desc _ _ _
    apply (cancel_epi πf).mp
    have h1 : πf ≫ (m ≫ e) = πf := by
      have ha : πf ≫ (m ≫ e) = (πf ≫ m) ≫ e := (Category.assoc πf m e).symm
      have hb : (πf ≫ m) ≫ e = (πf ≫ π0) ≫ e := congrArg (· ≫ e) hm
      have hc : (πf ≫ π0) ≫ e = πf ≫ (π0 ≫ e) := Category.assoc πf π0 e
      have hd : πf ≫ (π0 ≫ e) = πf ≫ 𝟙 _ := congrArg (πf ≫ ·) he
      have heq : πf ≫ 𝟙 (cokernel f.hom) = πf := by simp
      exact ha.trans (hb.trans (hc.trans (hd.trans heq)))
    have h2 : πf ≫ 𝟙 (cokernel f.hom) = πf := by simp
    exact h1.trans h2.symm
  right_triangle_components X := by
    have hX : cokernel.π (0 : (0 : C) ⟶ X) ≫ cokernelZeroIsoTarget.hom = 𝟙 X := by
      simp
    apply Arrow.hom_ext
    · exact HasZeroObject.from_zero_ext _ _
    · have hm : ((cokerUnit (C := C)).app (Arrow.zeroToFunctor.obj X)).right =
          cokernel.π (0 : (0 : C) ⟶ X) := rfl
      have h1 : ((cokerUnit (C := C)).app (Arrow.zeroToFunctor.obj X)).right ≫
          cokernelZeroIsoTarget.hom = 𝟙 X :=
        (congrArg (· ≫ cokernelZeroIsoTarget.hom) hm).trans hX
      exact h1

noncomputable instance cokerPreservesColimits :
    PreservesColimits (coker (C := C) : Arrow C ⥤ C) :=
  cokerAdjunction.leftAdjoint_preservesColimits

end Limits
end CategoryTheory
