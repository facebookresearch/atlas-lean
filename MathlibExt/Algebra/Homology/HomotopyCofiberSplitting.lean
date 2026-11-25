/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module


public import MathlibExt.Algebra.Homology.HomotopyCofiber
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Splittings of homotopy cofibers

The homotopy cofiber of a morphism with zero source is canonically isomorphic
to its target.  The comparison is natural for strict commutative squares and
is formulated for an arbitrary complex shape with predecessors.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C]
variable {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
variable {F G F' G' : HomologicalComplex C c}

/-- The null homotopy used by the zero-source projection. -/
noncomputable def zeroSourceHomotopy (f : F ⟶ G) (hF : IsZero F) :
    _root_.Homotopy (f ≫ 𝟙 G) 0 :=
  _root_.Homotopy.ofEq (by
    rw [Category.comp_id]
    exact hF.eq_of_src _ _)

/-- The canonical projection from a homotopy cofiber whose source is zero. -/
noncomputable def zeroSourceDesc (f : F ⟶ G) (hF : IsZero F) :
    HomologicalComplex.homotopyCofiber f ⟶ G :=
  desc f (𝟙 G) (zeroSourceHomotopy f hF)

/-- The target inclusion is a section of the zero-source projection. -/
@[reassoc (attr := simp)]
theorem inr_zeroSourceDesc (f : F ⟶ G) (hF : IsZero F) :
    inr f ≫ zeroSourceDesc f hF = 𝟙 G :=
  inr_desc f (𝟙 G) (zeroSourceHomotopy f hF)

/-- The zero-source projection is also a section of the target inclusion. -/
@[reassoc (attr := simp)]
theorem zeroSourceDesc_inr (f : F ⟶ G) (hF : IsZero F) :
    zeroSourceDesc f hF ≫ inr f =
      𝟙 (HomologicalComplex.homotopyCofiber f) := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : c.Rel i (c.next i)
  · apply ext_from_X f (c.next i) i hi
    · have hFi : IsZero (F.X (c.next i)) :=
        Functor.map_isZero
          (HomologicalComplex.eval C c (c.next i)) hF
      exact hFi.eq_of_src _ _
    · simp [zeroSourceDesc]
  · apply ext_from_X' f i hi
    simp [zeroSourceDesc]

/-- A homotopy cofiber with zero source is canonically isomorphic to its
target. -/
noncomputable def zeroSourceIso (f : F ⟶ G) (hF : IsZero F) :
    HomologicalComplex.homotopyCofiber f ≅ G where
  hom := zeroSourceDesc f hF
  inv := inr f
  hom_inv_id := zeroSourceDesc_inr f hF
  inv_hom_id := inr_zeroSourceDesc f hF

@[simp]
theorem zeroSourceIso_hom (f : F ⟶ G) (hF : IsZero F) :
    (zeroSourceIso f hF).hom = zeroSourceDesc f hF :=
  rfl

@[simp]
theorem zeroSourceIso_inv (f : F ⟶ G) (hF : IsZero F) :
    (zeroSourceIso f hF).inv = inr f :=
  rfl

/-- Naturality of the zero-source projection for a strict square. -/
@[reassoc]
theorem mapArrowHom_comp_zeroSourceDesc
    (H : ∀ j, ∃ i, c.Rel i j)
    (f : F ⟶ G) (f' : F' ⟶ G')
    (hF : IsZero F) (hF' : IsZero F')
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    mapArrowHom f f' H a ≫ zeroSourceDesc f' hF' =
      zeroSourceDesc f hF ≫ a.right := by
  apply mapArrowHom_desc_naturality H a
      (𝟙 G) (𝟙 G')
      (zeroSourceHomotopy f hF)
      (zeroSourceHomotopy f' hF') a.right
  · simp
  · intro i j
    simp [zeroSourceHomotopy]

/-- Naturality of the inverse of the zero-source comparison. -/
@[reassoc]
theorem zeroSourceIso_inv_comp_mapArrowHom
    (H : ∀ j, ∃ i, c.Rel i j)
    (f : F ⟶ G) (f' : F' ⟶ G')
    (hF : IsZero F) (hF' : IsZero F')
    (a : Arrow.mk f ⟶ Arrow.mk f') :
    (zeroSourceIso f hF).inv ≫ mapArrowHom f f' H a =
      a.right ≫ (zeroSourceIso f' hF').inv :=
  inr_mapArrowHom H a

/-- Arrows whose source object is zero. -/
def isZeroSourceArrow :
    ObjectProperty (Arrow (HomologicalComplex C c)) :=
  fun f ↦ IsZero f.left

/-- The full subcategory of arrows with zero source. -/
abbrev ZeroSourceArrow :=
  (isZeroSourceArrow (C := C) (c := c)).FullSubcategory

namespace ZeroSourceArrow

/-- Forget that an arrow has zero source. -/
abbrev inclusion :
    ZeroSourceArrow (C := C) (c := c) ⥤
      Arrow (HomologicalComplex C c) :=
  ObjectProperty.ι (isZeroSourceArrow (C := C) (c := c))

/-- On the full subcategory of arrows with zero source, the homotopy-cofiber
functor is naturally isomorphic to the target functor. -/
noncomputable def cofiberNatIso (H : ∀ j, ∃ i, c.Rel i j) :
    inclusion (C := C) (c := c) ⋙
        HomologicalComplex.homotopyCofiberFunctor H ≅
      inclusion (C := C) (c := c) ⋙ Arrow.rightFunc :=
  NatIso.ofComponents
    (fun f ↦ zeroSourceIso f.obj.hom f.property)
    (fun {f f'} a ↦ by
      exact mapArrowHom_comp_zeroSourceDesc H f.obj.hom f'.obj.hom
        f.property f'.property a.hom)

@[simp]
theorem cofiberNatIso_hom_app
    (H : ∀ j, ∃ i, c.Rel i j)
    (f : ZeroSourceArrow (C := C) (c := c)) :
    (cofiberNatIso H).hom.app f =
      zeroSourceDesc f.obj.hom f.property :=
  rfl

@[simp]
theorem cofiberNatIso_inv_app
    (H : ∀ j, ∃ i, c.Rel i j)
    (f : ZeroSourceArrow (C := C) (c := c)) :
    (cofiberNatIso H).inv.app f = inr f.obj.hom :=
  rfl

end ZeroSourceArrow

end HomologicalComplex.homotopyCofiber

end
