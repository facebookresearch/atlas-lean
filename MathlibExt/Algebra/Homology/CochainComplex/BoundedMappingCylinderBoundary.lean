/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedMappingCylinderCore
public import MathlibExt.CategoryTheory.Waldhausen.CoproductBiproductIso

/-!
# Boundary inclusions for bounded mapping cylinders

Let `C : Type uC` be preadditive with morphisms in universe `vC` and binary biproducts. For a
map `f : K ⟶ L` of bounded integer-indexed cochain complexes, write `Cyl(f)` for the homotopy
cofiber of `(1,−f) : K ⟶ K ⊞ L`. The endpoint maps induce a boundary `K ⊞ L ⟶ Cyl(f)`. After
forgetting boundedness, this is the canonical endpoint-biproduct chart followed by the cofiber
inclusion.

Every degree component of this boundary has a retraction, obtained by projecting the cofiber
onto its endpoint coordinate and applying the inverse chart. The boundary is therefore
degreewise split monic. If `C` has a zero object and a Waldhausen structure on `Bounded C` is
fixed, the chosen coproduct of the endpoints is canonically isomorphic to their biproduct.
Transporting the boundary and its degreewise retractions through this isomorphism gives the
corresponding chosen-coproduct formulas.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v uC vC

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

namespace CochainComplex.Bounded

variable (C : Type uC) [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]

/-- For a preadditive category `C` with binary biproducts and an arrow `f : K ⟶ L` in `Bounded C`, the canonical
isomorphism
`mappingCylinderBoundaryChart C f : (K ⊞ L : Bounded C).obj ≅ K.obj ⊞ L.obj`
is the biproduct comparison of the inclusion `ι C : Bounded C ⥤ CochainComplex C ℤ`. -/
def mappingCylinderBoundaryChart (f : Arrow (Bounded C)) :
    (f.left ⊞ f.right : Bounded C).obj ≅ f.left.obj ⊞ f.right.obj :=
  (ι C).mapBiprod f.left f.right

/-- Let `C` be preadditive with binary biproducts, and let `f : K ⟶ L` be a bounded integer-indexed cochain map. For the
mapping cylinder `Cyl(f) = Cof(1,−f)`, the boundary `K ⊞ L ⟶ Cyl(f)` is
`biprod.desc ((mappingCylinderFront C).app f) ((mappingCylinderBack C).app f)`.
Its restrictions to the two endpoint injections are the source and target maps of the cylinder. -/
def mappingCylinderBoundary (f : Arrow (Bounded C)) :
    (f.left ⊞ f.right : Bounded C) ⟶ (mappingCylinderFunctor C).obj f :=
  biprod.desc ((mappingCylinderFront C).app f) ((mappingCylinderBack C).app f)

/-- For a preadditive category `C` with binary biproducts and a bounded cochain arrow `f : K ⟶ L`,
`biprod.inl ≫ mappingCylinderBoundary C f = (mappingCylinderFront C).app f`.
Thus the boundary from `K ⊞ L` restricts on `K` to the source endpoint map `K ⟶ Cyl(f)`. -/
theorem mappingCylinderBoundary_inl (f : Arrow (Bounded C)) :
    biprod.inl ≫ mappingCylinderBoundary C f = (mappingCylinderFront C).app f :=
  biprod.inl_desc _ _

/-- For a preadditive category `C` with binary biproducts and a bounded cochain arrow `f : K ⟶ L`,
`biprod.inr ≫ mappingCylinderBoundary C f = (mappingCylinderBack C).app f`.
The boundary from `K ⊞ L` therefore restricts on `L` to the target endpoint map `L ⟶ Cyl(f)`. -/
theorem mappingCylinderBoundary_inr (f : Arrow (Bounded C)) :
    biprod.inr ≫ mappingCylinderBoundary C f = (mappingCylinderBack C).app f :=
  biprod.inr_desc _ _

/-- Let `C` be preadditive with binary biproducts, and let `f : K ⟶ L` be a map in `Bounded C`. Put `γ =
mappingCylinderBoundaryChart C f` and `χ = HomologicalComplex.mappingCylinder.arrow f.hom.hom = (1,−f.hom.hom)`. Then
the underlying cochain map of the boundary is
`(mappingCylinderBoundary C f).hom = γ.hom ≫ HomologicalComplex.homotopyCofiber.inr χ`.
Its domain is the underlying bounded biproduct and its target is `Cof(χ)`. -/
theorem mappingCylinderBoundary_hom (f : Arrow (Bounded C)) :
    (mappingCylinderBoundary C f).hom =
      (mappingCylinderBoundaryChart C f).hom ≫
        HomologicalComplex.homotopyCofiber.inr (HomologicalComplex.mappingCylinder.arrow f.hom.hom) := by
  let U := ι C
  have hdesc :
      biprod.desc (U.map ((mappingCylinderFront C).app f))
        (U.map ((mappingCylinderBack C).app f)) =
          HomologicalComplex.homotopyCofiber.inr (HomologicalComplex.mappingCylinder.arrow f.hom.hom) := by
    change biprod.desc (HomologicalComplex.mappingCylinder.source f.hom.hom)
      (HomologicalComplex.mappingCylinder.target f.hom.hom) = _
    apply biprod.hom_ext'
    · exact biprod.inl_desc _ _
    · exact biprod.inr_desc _ _
  calc
    _ = (mappingCylinderBoundaryChart C f).hom ≫
        biprod.desc (U.map ((mappingCylinderFront C).app f))
          (U.map ((mappingCylinderBack C).app f)) :=
      (biprod.mapBiprod_hom_desc U f.left f.right
        ((mappingCylinderFront C).app f) ((mappingCylinderBack C).app f)).symm
    _ = _ := congrArg (fun t => (mappingCylinderBoundaryChart C f).hom ≫ t) hdesc

/-- For a preadditive category `C` with binary biproducts, a bounded cochain arrow `f : K ⟶ L`, and `j : ℤ`, put `γ =
mappingCylinderBoundaryChart C f` and `χ = (1,−f.hom.hom)`. The degree-`j` boundary component satisfies
`(mappingCylinderBoundary C f).hom.f j = γ.hom.f j ≫ HomologicalComplex.homotopyCofiber.inrX χ j`.
It is the biproduct chart in degree `j` followed by the cofiber's endpoint-coordinate inclusion. -/
theorem mappingCylinderBoundary_f (f : Arrow (Bounded C)) (j : ℤ) :
    (mappingCylinderBoundary C f).hom.f j =
      (mappingCylinderBoundaryChart C f).hom.f j ≫
        HomologicalComplex.homotopyCofiber.inrX
          (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j := by
  exact HomologicalComplex.congr_hom (mappingCylinderBoundary_hom C f) j

/-- Let `C` be preadditive with binary biproducts, `f : K ⟶ L` a bounded cochain arrow, and `j : ℤ`. Put `γ =
mappingCylinderBoundaryChart C f` and `χ = (1,−f.hom.hom)`. The morphism
`Cyl(f).obj.X j ⟶ (K ⊞ L : Bounded C).obj.X j`
is `HomologicalComplex.homotopyCofiber.sndX χ j ≫ γ.inv.f j`. It projects onto the cofiber's endpoint coordinate and
then identifies it with the selected bounded biproduct term. -/
def mappingCylinderBoundaryRetraction (f : Arrow (Bounded C)) (j : ℤ) :
    ((mappingCylinderFunctor C).obj f).obj.X j ⟶ (f.left ⊞ f.right : Bounded C).obj.X j :=
  HomologicalComplex.homotopyCofiber.sndX (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j ≫
    (mappingCylinderBoundaryChart C f).inv.f j

/-- For a preadditive category `C` with binary biproducts, a bounded cochain arrow `f : K ⟶ L`, and `j : ℤ`,
`(mappingCylinderBoundary C f).hom.f j ≫ mappingCylinderBoundaryRetraction C f j = 𝟙 ((K ⊞ L : Bounded C).obj.X j)`.
The endpoint-coordinate projection, followed by the inverse biproduct chart, retracts the boundary in each degree. -/
theorem mappingCylinderBoundary_f_retraction (f : Arrow (Bounded C)) (j : ℤ) :
    (mappingCylinderBoundary C f).hom.f j ≫ mappingCylinderBoundaryRetraction C f j =
      𝟙 ((f.left ⊞ f.right : Bounded C).obj.X j) := by
  let e := HomologicalComplex.Hom.isoApp (mappingCylinderBoundaryChart C f) j
  let i := HomologicalComplex.homotopyCofiber.inrX
    (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j
  let r := HomologicalComplex.homotopyCofiber.sndX
    (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j
  have hir : i ≫ r = 𝟙 ((f.left.obj ⊞ f.right.obj).X j) :=
    HomologicalComplex.homotopyCofiber.inrX_sndX
      (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j
  rw [mappingCylinderBoundary_f]
  change (e.hom ≫ i) ≫ (r ≫ e.inv) = 𝟙 _
  calc
    _ = e.hom ≫ ((i ≫ r) ≫ e.inv) :=
      (Category.assoc e.hom i (r ≫ e.inv)).trans
        (congrArg (fun t => e.hom ≫ t) (Category.assoc i r e.inv).symm)
    _ = e.hom ≫ (𝟙 _ ≫ e.inv) :=
      congrArg (fun t => e.hom ≫ (t ≫ e.inv)) hir
    _ = e.hom ≫ e.inv := congrArg (fun t => e.hom ≫ t) (Category.id_comp e.inv)
    _ = 𝟙 _ := e.hom_inv_id

/-- Let `C` be preadditive with binary biproducts and let `f : K ⟶ L` be a bounded integer-indexed
cochain arrow. Then `degreewiseSplitMonomorphisms C (mappingCylinderBoundary C f)` holds. In
degree `j`, the splitting is `mappingCylinderBoundaryRetraction C f j`, whose composite after
the boundary component is the identity of the endpoint-biproduct term. -/
theorem mappingCylinderBoundary_degreewiseSplit (f : Arrow (Bounded C)) :
    degreewiseSplitMonomorphisms C (mappingCylinderBoundary C f) :=
  fun j => IsSplitMono.mk' ⟨mappingCylinderBoundaryRetraction C f j,
    mappingCylinderBoundary_f_retraction C f j⟩

end CochainComplex.Bounded

namespace CochainComplex.Bounded

variable (C : Type uC) [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]
  [HasZeroObject C] [WaldhausenCategoryWithoutGluing (Bounded C)]

/-- Let `C` be preadditive with a zero object and binary biproducts, and fix a Waldhausen
structure on `Bounded C`. For an arrow `f : K ⟶ L` in `Bounded C`,
`mappingCylinderCoproductCofan C f : BinaryCofan K L` is the chosen colimiting coproduct cofan
obtained from the Waldhausen zero-pushout construction. -/
def mappingCylinderCoproductCofan (f : Arrow (Bounded C)) : BinaryCofan f.left f.right :=
  (Waldhausen.binaryCoproductColimitCocone (Bounded C) (pair f.left f.right)).cocone

/-- For a preadditive category `C` with a zero object and binary biproducts and a fixed Waldhausen structure on `Bounded
C`, let `f : K ⟶ L` be an arrow. The canonical isomorphism
`(mappingCylinderCoproductCofan C f).pt ≅ K ⊞ L`
identifies the chosen coproduct of the endpoints with their selected biproduct in `Bounded C`. -/
def mappingCylinderCoproductBiproductIso (f : Arrow (Bounded C)) :
    (mappingCylinderCoproductCofan C f).pt ≅ f.left ⊞ f.right :=
  (eqToIso (Waldhausen.waldhausenCoproductFunctor_obj (Bounded C) (f.left, f.right))).symm ≪≫
    (Waldhausen.coproductBiproductNatIso (Bounded C)).app (f.left, f.right)

/-- Let `C` be preadditive with a zero object and binary biproducts and a fixed Waldhausen structure on `Bounded C`. For
an arrow `f : K ⟶ L`,
`(mappingCylinderCoproductBiproductIso C f).hom = (Waldhausen.binaryCoproductBiproductIso (Bounded C) K L).hom`.
Both maps identify the chosen zero-pushout coproduct of `K, L` with their selected biproduct. -/
theorem mappingCylinderCoproductBiproductIso_hom (f : Arrow (Bounded C)) :
    (mappingCylinderCoproductBiproductIso C f).hom =
      (Waldhausen.binaryCoproductBiproductIso (Bounded C) f.left f.right).hom := by
  let e := eqToIso (Waldhausen.waldhausenCoproductFunctor_obj (Bounded C) (f.left, f.right))
  have h : (Waldhausen.coproductBiproductNatIso (Bounded C)).hom.app (f.left, f.right) =
      e.hom ≫ (Waldhausen.binaryCoproductBiproductIso (Bounded C) f.left f.right).hom :=
    Waldhausen.coproductBiproductNatIso_hom_app (Bounded C) f.left f.right
  calc
    _ = e.inv ≫ (e.hom ≫
        (Waldhausen.binaryCoproductBiproductIso (Bounded C) f.left f.right).hom) :=
      congrArg (fun t => e.inv ≫ t) h
    _ = _ := e.inv_hom_id_assoc _

/-- Let `C` be preadditive with a zero object and binary biproducts, with a fixed Waldhausen structure on `Bounded C`,
and let `f : K ⟶ L` be an arrow. The map from the chosen endpoint coproduct to `Cyl(f)` is
`mappingCylinderCoproductBoundary C f = (mappingCylinderCoproductBiproductIso C f).hom ≫ mappingCylinderBoundary C f`.
It transports the biproduct boundary along the canonical coproduct comparison. -/
def mappingCylinderCoproductBoundary (f : Arrow (Bounded C)) :
    (mappingCylinderCoproductCofan C f).pt ⟶ (mappingCylinderFunctor C).obj f :=
  (mappingCylinderCoproductBiproductIso C f).hom ≫
    mappingCylinderBoundary C f

/-- For a preadditive category `C` with a zero object and binary biproducts, a fixed Waldhausen structure on `Bounded
C`, and an arrow `f : K ⟶ L`,
`mappingCylinderCoproductBoundary C f = (mappingCylinderCoproductBiproductIso C f).hom ≫ mappingCylinderBoundary C f`.
The equality expresses the boundary with domain the chosen coproduct as the comparison to the endpoint biproduct
followed by its boundary. -/
theorem mappingCylinderCoproductBoundary_eq (f : Arrow (Bounded C)) :
    mappingCylinderCoproductBoundary C f =
      (mappingCylinderCoproductBiproductIso C f).hom ≫
        mappingCylinderBoundary C f := rfl

/-- Let `C` be preadditive with a zero object and binary biproducts, with a fixed Waldhausen structure on `Bounded C`,
and let `f : K ⟶ L` be an arrow. The first leg of the chosen endpoint coproduct satisfies
`(mappingCylinderCoproductCofan C f).inl ≫ mappingCylinderCoproductBoundary C f = (mappingCylinderFront C).app f`.
Its composite with the boundary is the source endpoint map `K ⟶ Cyl(f)`. -/
theorem mappingCylinderCoproductBoundary_inl (f : Arrow (Bounded C)) :
    (mappingCylinderCoproductCofan C f).inl ≫ mappingCylinderCoproductBoundary C f =
      (mappingCylinderFront C).app f := by
  have h : (mappingCylinderCoproductCofan C f).inl ≫
      (mappingCylinderCoproductBiproductIso C f).hom = biprod.inl := by
    rw [mappingCylinderCoproductBiproductIso_hom]
    exact Waldhausen.binaryCoproductBiproductIso_inl_hom (Bounded C) f.left f.right
  calc
    _ = ((mappingCylinderCoproductCofan C f).inl ≫
        (mappingCylinderCoproductBiproductIso C f).hom) ≫
          mappingCylinderBoundary C f := (Category.assoc _ _ _).symm
    _ = biprod.inl ≫ mappingCylinderBoundary C f :=
      congrArg (fun t => t ≫ mappingCylinderBoundary C f) h
    _ = _ := mappingCylinderBoundary_inl C f

/-- For a preadditive category `C` with a zero object and binary biproducts, a fixed Waldhausen structure on `Bounded
C`, and an arrow `f : K ⟶ L`,
`(mappingCylinderCoproductCofan C f).inr ≫ mappingCylinderCoproductBoundary C f = (mappingCylinderBack C).app f`.
The second leg of the chosen endpoint coproduct therefore reaches the target endpoint map `L ⟶ Cyl(f)`. -/
theorem mappingCylinderCoproductBoundary_inr (f : Arrow (Bounded C)) :
    (mappingCylinderCoproductCofan C f).inr ≫ mappingCylinderCoproductBoundary C f =
      (mappingCylinderBack C).app f := by
  have h : (mappingCylinderCoproductCofan C f).inr ≫
      (mappingCylinderCoproductBiproductIso C f).hom = biprod.inr := by
    rw [mappingCylinderCoproductBiproductIso_hom]
    exact Waldhausen.binaryCoproductBiproductIso_inr_hom (Bounded C) f.left f.right
  calc
    _ = ((mappingCylinderCoproductCofan C f).inr ≫
        (mappingCylinderCoproductBiproductIso C f).hom) ≫
          mappingCylinderBoundary C f := (Category.assoc _ _ _).symm
    _ = biprod.inr ≫ mappingCylinderBoundary C f :=
      congrArg (fun t => t ≫ mappingCylinderBoundary C f) h
    _ = _ := mappingCylinderBoundary_inr C f

/-- Let `C` be preadditive with a zero object and binary biproducts, with a fixed Waldhausen structure on `Bounded C`,
and let `f : K ⟶ L` and `j : ℤ`. Put `e = mappingCylinderCoproductBiproductIso C f`. Then
`(mappingCylinderCoproductBoundary C f).hom.f j = e.hom.hom.f j ≫ (mappingCylinderBoundary C f).hom.f j`.
The component first identifies the chosen coproduct term with the biproduct term and then applies the boundary
component. -/
theorem mappingCylinderCoproductBoundary_f (f : Arrow (Bounded C)) (j : ℤ) :
    (mappingCylinderCoproductBoundary C f).hom.f j =
      ((mappingCylinderCoproductBiproductIso C f).hom).hom.f j ≫
        (mappingCylinderBoundary C f).hom.f j := rfl

/-- Let `C` be preadditive with a zero object and binary biproducts, with a fixed Waldhausen structure on `Bounded C`,
and let `f : K ⟶ L` and `j : ℤ`. Put `e = mappingCylinderCoproductBiproductIso C f`. The degreewise map from `Cyl(f)` to
the chosen endpoint coproduct is
`mappingCylinderBoundaryRetraction C f j ≫ e.inv.hom.f j`.
Its target is `((mappingCylinderCoproductCofan C f).pt).obj.X j`. -/
def mappingCylinderCoproductBoundaryRetraction (f : Arrow (Bounded C)) (j : ℤ) :
    ((mappingCylinderFunctor C).obj f).obj.X j ⟶ (mappingCylinderCoproductCofan C f).pt.obj.X j :=
  mappingCylinderBoundaryRetraction C f j ≫
    ((mappingCylinderCoproductBiproductIso C f).inv).hom.f j

/-- For a preadditive category `C` with a zero object and binary biproducts, a fixed Waldhausen structure on `Bounded
C`, an arrow `f : K ⟶ L`, and `j : ℤ`,
`(mappingCylinderCoproductBoundary C f).hom.f j ≫ mappingCylinderCoproductBoundaryRetraction C f j = 𝟙
((mappingCylinderCoproductCofan C f).pt.obj.X j)`.
Thus the transported degreewise projection retracts the chosen-coproduct boundary. -/
theorem mappingCylinderCoproductBoundary_f_retraction (f : Arrow (Bounded C)) (j : ℤ) :
    (mappingCylinderCoproductBoundary C f).hom.f j ≫
      mappingCylinderCoproductBoundaryRetraction C f j =
        𝟙 ((mappingCylinderCoproductCofan C f).pt.obj.X j) := by
  let e := mappingCylinderCoproductBiproductIso C f
  change (e.hom.hom.f j ≫ (mappingCylinderBoundary C f).hom.f j) ≫
    (mappingCylinderBoundaryRetraction C f j ≫ e.inv.hom.f j) = _
  calc
    _ = e.hom.hom.f j ≫ (((mappingCylinderBoundary C f).hom.f j ≫
        mappingCylinderBoundaryRetraction C f j) ≫ e.inv.hom.f j) := by
      simp only [Category.assoc]
    _ = e.hom.hom.f j ≫ ((𝟙 _) ≫ e.inv.hom.f j) :=
      congrArg (fun t => e.hom.hom.f j ≫ (t ≫ e.inv.hom.f j))
        (mappingCylinderBoundary_f_retraction C f j)
    _ = e.hom.hom.f j ≫ e.inv.hom.f j := by rw [Category.id_comp]
    _ = _ := (HomologicalComplex.Hom.isoApp ((ι C).mapIso e) j).hom_inv_id

/-- Let `C` be preadditive with a zero object and binary biproducts, with a fixed Waldhausen structure on `Bounded C`.
For every bounded cochain arrow `f : K ⟶ L`, the map from the chosen endpoint coproduct to `Cyl(f)` is degreewise split
monic:
`degreewiseSplitMonomorphisms C (mappingCylinderCoproductBoundary C f)`.
Its splitting in degree `j` is `mappingCylinderCoproductBoundaryRetraction C f j`. -/
theorem mappingCylinderCoproductBoundary_degreewiseSplit (f : Arrow (Bounded C)) :
    degreewiseSplitMonomorphisms C (mappingCylinderCoproductBoundary C f) :=
  fun j => IsSplitMono.mk' ⟨mappingCylinderCoproductBoundaryRetraction C f j,
    mappingCylinderCoproductBoundary_f_retraction C f j⟩

end CochainComplex.Bounded

end
