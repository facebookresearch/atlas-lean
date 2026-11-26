/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.CochainComplex.Bounded
public import MathlibExt.Algebra.Homology.HomologicalComplexBiprodMaps
public import MathlibExt.Algebra.Homology.FiniteSupportConeAugmentation
public import MathlibExt.Algebra.Homology.MappingCylinderQuasiIso
public import MathlibExt.CategoryTheory.Waldhausen.MappingCylinderCore

/-!
# Mapping cylinders of bounded cochain complexes

Let C be a preadditive category with binary biproducts. For a map f:K → L
of integer-indexed cochain complexes, its mapping cylinder is the homotopy
cofiber of (1,−f):K → K ⊞ L. In degree j it has the biproduct chart
Cyl(f)ʲ ≅ Kʲ⁺¹ ⊞ (Kʲ ⊞ Lʲ).

If K and L are supported in [a,b] and [c,e], then Cyl(f) is supported in
[min(a−1,min(a,c)),max(b−1,max(b,e))]. Thus the cylinder is a functor
from arrows of bounded complexes to bounded complexes. Its source and
target inclusions and its projection to L are natural in commuting squares.
The projection composed after the source inclusion is f, and after the
target inclusion is 1. Both endpoint inclusions admit retractions in each
degree.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v uC vC

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CochainComplex.Bounded

/-- In the integer-indexed cochain shape, every degree j has the predecessor
j−1: the differential relation holds from j−1 to j. -/
theorem mappingCylinderPredecessors : ∀ j : ℤ, ∃ i : ℤ, (ComplexShape.up ℤ).Rel i j :=
  fun j => ⟨j - 1, by change (j - 1) + 1 = j; omega⟩

variable (C : Type uC) [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]

/-- Let C be preadditive with binary biproducts, and let f:K → L be a map
of integer-indexed cochain complexes. If Kʲ is zero outside [a,b] and Lʲ is
zero outside [c,e], then the j-th term of the mapping cylinder, the homotopy
cofiber of (1,−f):K → K ⊞ L, is zero whenever
j<min(a−1,min(a,c)) or max(b−1,max(b,e))<j. -/
theorem mappingCylinder_isZero_outside {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (a b c e : ℤ)
    (hK : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j))
    (hL : ∀ j : ℤ, j < c ∨ e < j → IsZero (L.X j))
    (j : ℤ) (hj : j < min (a - 1) (min a c) ∨ max (b - 1) (max b e) < j) :
    IsZero ((HomologicalComplex.mappingCylinder f).X j) :=
  CochainComplex.mappingCone.isZero_outside_of_finiteSupport
    (HomologicalComplex.mappingCylinder.arrow f) a b (min a c) (max b e) hK
    (CochainComplex.biprod_isZero_outside C K L a b c e hK hL) j hj

/-- In a preadditive category C with binary biproducts, the mapping cylinder
of every map f:K → L between bounded integer-indexed cochain complexes is
bounded. If the endpoints have support intervals [a,b] and [c,e], a support
interval for the cylinder is
[min(a−1,min(a,c)),max(b−1,max(b,e))]. -/
theorem mappingCylinder_bounded {K L : Bounded C} (f : K ⟶ L) :
    CochainComplex.bounded C (HomologicalComplex.mappingCylinder f.hom) := by
  obtain ⟨a, b, hK⟩ := K.property
  obtain ⟨c, e, hL⟩ := L.property
  exact ⟨min (a - 1) (min a c), max (b - 1) (max b e),
    mappingCylinder_isZero_outside C f.hom a b c e hK hL⟩

/-- For a preadditive category C with binary biproducts, the functor from
arrows of bounded integer-indexed cochain complexes to bounded complexes
that sends f:K → L to the homotopy cofiber of (1,−f):K → K ⊞ L.
A commuting square of endpoint maps induces the corresponding map of
mapping cylinders. -/
def mappingCylinderFunctor : Arrow (Bounded C) ⥤ Bounded C :=
  ObjectProperty.lift (CochainComplex.bounded C)
    ((ι C).mapArrow ⋙ HomologicalComplex.mappingCylinder.functor mappingCylinderPredecessors)
    (fun f => mappingCylinder_bounded C f.hom)

/-- For a preadditive category C with binary biproducts and an arrow
f:K → L of bounded cochain complexes, forgetting boundedness from its
cylinder gives the homotopy cofiber of (1,−f):K → K ⊞ L in the category
of all integer-indexed cochain complexes. -/
theorem mappingCylinderFunctor_obj_obj (f : Arrow (Bounded C)) :
    ((mappingCylinderFunctor C).obj f).obj = HomologicalComplex.mappingCylinder f.hom.hom := rfl

/-- In a preadditive category C with binary biproducts, a commuting square
from f:K → L to g:K′ → L′ of bounded cochain complexes is sent by the
bounded cylinder functor to the same cochain map as the canonical
mapping-cylinder construction on that square. -/
theorem mappingCylinderFunctor_map_hom {f g : Arrow (Bounded C)} (a : f ⟶ g) :
    ((mappingCylinderFunctor C).map a).hom =
      HomologicalComplex.mappingCylinder.map f.hom.hom g.hom.hom mappingCylinderPredecessors
        ((ι C).mapArrow.map a) := rfl

/-- Let C be preadditive with binary biproducts, f:K → L a bounded cochain
map, and j an integer. The canonical term isomorphism
Cyl(f)ʲ ≅ Kʲ⁺¹ ⊞ (Kʲ ⊞ Lʲ), obtained from the cofiber of
(1,−f):K → K ⊞ L and the endpoint biproduct. -/
def mappingCylinderTermIso (f : Arrow (Bounded C)) (j : ℤ) :
    ((mappingCylinderFunctor C).obj f).obj.X j ≅
      f.left.obj.X (j + 1) ⊞ (f.left.obj.X j ⊞ f.right.obj.X j) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod
    (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j (j + 1) rfl ≪≫
      biprod.mapIso (Iso.refl _) (HomologicalComplex.biprodXIso f.left.obj f.right.obj j)

/-- In a preadditive category C with binary biproducts, the natural
transformation from the source of a bounded cochain arrow f:K → L to
its mapping cylinder. Its component is the inclusion of K into the
endpoint biproduct K ⊞ L followed by the cofiber inclusion for (1,−f). -/
def mappingCylinderFront : (Arrow.leftFunc : Arrow (Bounded C) ⥤ Bounded C) ⟶
    mappingCylinderFunctor C where
  app f := ObjectProperty.homMk
    ((HomologicalComplex.mappingCylinder.sourceNatTrans mappingCylinderPredecessors).app
      ((ι C).mapArrow.obj f))
  naturality {f g} a := by
    apply ObjectProperty.hom_ext
    exact (HomologicalComplex.mappingCylinder.sourceNatTrans mappingCylinderPredecessors).naturality
      ((ι C).mapArrow.map a)

/-- In a preadditive category C with binary biproducts, the natural
transformation from the target of a bounded cochain arrow f:K → L to
its mapping cylinder. Its component is the inclusion of L into K ⊞ L
followed by the cofiber inclusion for (1,−f). -/
def mappingCylinderBack : (Arrow.rightFunc : Arrow (Bounded C) ⥤ Bounded C) ⟶
    mappingCylinderFunctor C where
  app f := ObjectProperty.homMk
    ((HomologicalComplex.mappingCylinder.targetNatTrans mappingCylinderPredecessors).app
      ((ι C).mapArrow.obj f))
  naturality {f g} a := by
    apply ObjectProperty.hom_ext
    exact (HomologicalComplex.mappingCylinder.targetNatTrans mappingCylinderPredecessors).naturality
      ((ι C).mapArrow.map a)

/-- In a preadditive category C with binary biproducts, the natural
projection Cyl(f) → L for each bounded cochain arrow f:K → L.
It is induced from the endpoint map [f,1]:K ⊞ L → L, whose composite
with (1,−f):K → K ⊞ L is zero. -/
def mappingCylinderProjection : mappingCylinderFunctor C ⟶
    (Arrow.rightFunc : Arrow (Bounded C) ⥤ Bounded C) where
  app f := ObjectProperty.homMk
    ((HomologicalComplex.mappingCylinder.projectionNatTrans mappingCylinderPredecessors).app
      ((ι C).mapArrow.obj f))
  naturality {f g} a := by
    apply ObjectProperty.hom_ext
    exact (HomologicalComplex.mappingCylinder.projectionNatTrans mappingCylinderPredecessors).naturality
      ((ι C).mapArrow.map a)

/-- For a bounded cochain arrow f:K → L in a preadditive category C with
binary biproducts, the underlying map of the bounded source inclusion
K → Cyl(f) is the source inclusion into the cofiber of
(1,−f):K → K ⊞ L. -/
theorem mappingCylinderFront_app_hom (f : Arrow (Bounded C)) :
    ((mappingCylinderFront C).app f).hom = HomologicalComplex.mappingCylinder.source f.hom.hom := rfl

/-- For a bounded cochain arrow f:K → L in a preadditive category C with
binary biproducts, the underlying map of the bounded target inclusion
L → Cyl(f) is the target inclusion into the cofiber of
(1,−f):K → K ⊞ L. -/
theorem mappingCylinderBack_app_hom (f : Arrow (Bounded C)) :
    ((mappingCylinderBack C).app f).hom = HomologicalComplex.mappingCylinder.target f.hom.hom := rfl

/-- For a bounded cochain arrow f:K → L in a preadditive category C with
binary biproducts, the underlying map of the bounded projection Cyl(f) → L
is the cofiber projection induced by [f,1]:K ⊞ L → L. -/
theorem mappingCylinderProjection_app_hom (f : Arrow (Bounded C)) :
    ((mappingCylinderProjection C).app f).hom = HomologicalComplex.mappingCylinder.projection f.hom.hom := rfl

/-- For a preadditive category C with binary biproducts, the composite of
the natural source inclusion K → Cyl(f) with the natural projection
Cyl(f) → L equals f:K → L for every bounded cochain arrow. Equivalently,
this composite is the natural transformation from source to target in
the arrow category. -/
theorem mappingCylinderFront_projection :
    mappingCylinderFront C ≫ mappingCylinderProjection C = Arrow.leftToRight := by
  apply NatTrans.ext
  funext f
  apply ObjectProperty.hom_ext
  exact HomologicalComplex.mappingCylinder.source_projection f.hom.hom

/-- For a preadditive category C with binary biproducts, the natural target
inclusion L → Cyl(f) is a section of the natural projection Cyl(f) → L
on bounded cochain arrows: their composite on L is its identity. -/
theorem mappingCylinderBack_projection :
    mappingCylinderBack C ≫ mappingCylinderProjection C =
      (𝟙 _ : (Arrow.rightFunc : Arrow (Bounded C) ⥤ Bounded C) ⟶ Arrow.rightFunc) := by
  apply NatTrans.ext
  funext f
  apply ObjectProperty.hom_ext
  exact HomologicalComplex.mappingCylinder.target_projection f.hom.hom

/-- Let C be preadditive with binary biproducts, f:K → L a bounded cochain
map, and j an integer. The map Cyl(f)ʲ → Kʲ that projects through the
cofiber's endpoint coordinate Kʲ ⊞ Lʲ onto Kʲ. It retracts the source
endpoint inclusion in degree j. -/
def mappingCylinderFrontRetraction (f : Arrow (Bounded C)) (j : ℤ) :
    ((mappingCylinderFunctor C).obj f).obj.X j ⟶ f.left.obj.X j :=
  HomologicalComplex.homotopyCofiber.sndX (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j ≫
    (biprod.fst : f.left.obj ⊞ f.right.obj ⟶ f.left.obj).f j

/-- Let C be preadditive with binary biproducts, f:K → L a bounded cochain
map, and j an integer. The map Cyl(f)ʲ → Lʲ that projects through the
cofiber's endpoint coordinate Kʲ ⊞ Lʲ onto Lʲ. It retracts the target
endpoint inclusion in degree j. -/
def mappingCylinderBackRetraction (f : Arrow (Bounded C)) (j : ℤ) :
    ((mappingCylinderFunctor C).obj f).obj.X j ⟶ f.right.obj.X j :=
  HomologicalComplex.homotopyCofiber.sndX (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j ≫
    (biprod.snd : f.left.obj ⊞ f.right.obj ⟶ f.right.obj).f j

/-- For a bounded cochain map f:K → L in a preadditive category C with
binary biproducts, the source inclusion Kʲ → Cyl(f)ʲ followed by projection
onto the Kʲ endpoint coordinate is the identity of Kʲ for every integer j. -/
theorem mappingCylinderFront_f_retraction (f : Arrow (Bounded C)) (j : ℤ) :
    ((mappingCylinderFront C).app f).hom.f j ≫ mappingCylinderFrontRetraction C f j =
      𝟙 (f.left.obj.X j) := by
  change ((biprod.inl : f.left.obj ⟶ f.left.obj ⊞ f.right.obj).f j ≫
    HomologicalComplex.homotopyCofiber.inrX (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j) ≫
      (HomologicalComplex.homotopyCofiber.sndX
        (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j ≫
          (biprod.fst : f.left.obj ⊞ f.right.obj ⟶ f.left.obj).f j) = _
  simp only [Category.assoc, HomologicalComplex.homotopyCofiber.inrX_sndX_assoc,
    HomologicalComplex.biprod_inl_fst_f]

/-- For a bounded cochain map f:K → L in a preadditive category C with
binary biproducts, the target inclusion Lʲ → Cyl(f)ʲ followed by projection
onto the Lʲ endpoint coordinate is the identity of Lʲ for every integer j. -/
theorem mappingCylinderBack_f_retraction (f : Arrow (Bounded C)) (j : ℤ) :
    ((mappingCylinderBack C).app f).hom.f j ≫ mappingCylinderBackRetraction C f j =
      𝟙 (f.right.obj.X j) := by
  change ((biprod.inr : f.right.obj ⟶ f.left.obj ⊞ f.right.obj).f j ≫
    HomologicalComplex.homotopyCofiber.inrX (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j) ≫
      (HomologicalComplex.homotopyCofiber.sndX
        (HomologicalComplex.mappingCylinder.arrow f.hom.hom) j ≫
          (biprod.snd : f.left.obj ⊞ f.right.obj ⟶ f.right.obj).f j) = _
  simp only [Category.assoc, HomologicalComplex.homotopyCofiber.inrX_sndX_assoc,
    HomologicalComplex.biprod_inr_snd_f]

/-- In a preadditive category C with binary biproducts, both endpoint maps
K → Cyl(f) and L → Cyl(f) of a bounded cochain map f:K → L are split
monomorphisms in each integer degree, with retractions given by the
corresponding endpoint-coordinate projections. -/
theorem mappingCylinder_endpoints_split (f : Arrow (Bounded C)) :
    degreewiseSplitMonomorphisms C ((mappingCylinderFront C).app f) ∧
      degreewiseSplitMonomorphisms C ((mappingCylinderBack C).app f) := by
  exact ⟨fun j => IsSplitMono.mk' ⟨mappingCylinderFrontRetraction C f j,
    mappingCylinderFront_f_retraction C f j⟩,
    fun j => IsSplitMono.mk' ⟨mappingCylinderBackRetraction C f j,
      mappingCylinderBack_f_retraction C f j⟩⟩

end CochainComplex.Bounded

end
