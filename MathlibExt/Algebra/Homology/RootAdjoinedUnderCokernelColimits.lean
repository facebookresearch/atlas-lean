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

public import MathlibExt.Algebra.Homology.UnderCokernelSupport
public import Mathlib.CategoryTheory.WithTerminal.Cone

/-!
# Colimits after adjoining the fixed source to carrier diagrams

Let C be abelian, c a complex shape on ℤ, and I a fixed complex. Consider arrows a:I→X whose
cokernel complexes have zero terms below degree zero. To a diagram D of these arrows, adjoin an
initial index ★ with value I and maps ★→j equal to the source arrows a_j.

A colimit of this enlarged carrier diagram gives the supported under colimit: its target is the
carrier point, its source arrow is the ★-leg, and its other legs are the carrier legs. Cokernel
reduction then gives a colimit of the reduced complexes. This construction applies to arbitrary
J, including empty and disconnected shapes, when the specified colimits exist.

The supported identity arrow id_I is initial in the under category. Its binary coproduct with
itself has the same identity vertex and identity legs. If I is nonzero, the bare target
forgetful functor does not preserve this coproduct; the fixed source is essential to the
enlarged carrier diagram.
-/

@[expose] public section

noncomputable section

universe v u w w'

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {c : ComplexShape ℤ}
variable (I : HomologicalComplex C c)
variable {J : Type w} [Category.{w'} J]

/-- Let C be abelian in object/morphism universes u,v, c a complex shape on ℤ, and I a c-shaped
complex. Let 𝒰_I be arrows I→X with cokernel terms zero in degrees n<0. For a category J in
independent universes w,w' and D:J→𝒰_I, the diagram on WithInitial(J) has object I at ★ and X_j
at j. Its new map ★→j is the source arrow a_j:I→X_j, and its remaining maps are the target
components of D. -/
abbrev rootAdjoinedUnderCokernelDiagram
    (D : J ⥤ (underCokernelNonnegativeProperty I).FullSubcategory) :
    WithInitial J ⥤ HomologicalComplex C c :=
  WithInitial.liftFromUnder.obj (D ⋙ (underCokernelNonnegativeProperty I).ι)

/-- Let C be abelian in object/morphism universes u,v, c a complex shape on ℤ, and I a c-shaped
complex. Let 𝒰_I be arrows I→X with cokernel terms zero in degrees n<0. For a category J in
object/morphism universes w,w' and D:J→𝒰_I, adjoin an initial index ★ to J: its carrier diagram
has value I at ★, the target X_j at j, and source arrow a_j:I→X_j on ★→j. For any cocone s, the
recovered cocone in Under(I) has vertex s_★:I→s.pt and leg at j with carrier component s_j.
Naturality of s gives a_j≫s_j=s_★. -/
abbrev underCoconeFromRoot {D : J ⥤ (underCokernelNonnegativeProperty I).FullSubcategory}
    (s : Cocone (rootAdjoinedUnderCokernelDiagram I D)) :
    Cocone (D ⋙ (underCokernelNonnegativeProperty I).ι) :=
  WithInitial.coconeEquiv.inverse.obj s

/-- Let C be abelian in object/morphism universes u,v, c a complex shape on ℤ, and I a c-shaped
complex. Let 𝒰_I be arrows I→X with cokernel terms zero in degrees n<0. For a category J in
object/morphism universes w,w' and D:J→𝒰_I, adjoin an initial index ★ to J: its carrier diagram
has value I at ★, the target X_j at j, and source arrow a_j:I→X_j on ★→j. If s is a colimit
cocone of the root-adjoined diagram, its recovered cocone is colimiting in Under(I) for the
included diagram D. The cocone equivalence identifies the universal properties. -/
def isColimitUnderCoconeFromRoot
    {D : J ⥤ (underCokernelNonnegativeProperty I).FullSubcategory}
    {s : Cocone (rootAdjoinedUnderCokernelDiagram I D)} (hs : IsColimit s) :
    IsColimit (underCoconeFromRoot I s) :=
  WithInitial.isColimitEquiv
    (IsColimit.ofIsoColimit hs (WithInitial.coconeEquiv.counitIso.app s).symm)

section Colimits

variable [HasColimitsOfShape J C]
variable {D : J ⥤ (underCokernelNonnegativeProperty I).FullSubcategory}
variable {s : Cocone (rootAdjoinedUnderCokernelDiagram I D)} (hs : IsColimit s)

/-- Let C be abelian in object/morphism universes u,v, c a complex shape on ℤ, and I a c-shaped
complex. Let 𝒰_I be arrows I→X with cokernel terms zero in degrees n<0. For a category J in
object/morphism universes w,w' and D:J→𝒰_I, adjoin an initial index ★ to J: its carrier diagram
has value I at ★, the target X_j at j, and source arrow a_j:I→X_j on ★→j. Let J have
object/morphism universes w,w', assume C has J-colimits, and let s be a colimit cocone of this
root-adjoined carrier diagram. Write a=s_★:I→s.pt and λ_j=s_j:X_j→s.pt. The supported cocone has
vertex a:I→s.pt and carrier legs λ_j. Its cokernel has zero terms below degree zero, obtained
from the colimit of the diagram's cokernel reductions. -/
def rootAdjoinedUnderCokernelCocone : Cocone D where
  pt := ⟨(underCoconeFromRoot I s).pt,
    underCokernelNonnegativeProperty_of_isColimit I
    (isColimitUnderCoconeFromRoot I hs) (fun j => (D.obj j).property)⟩
  ι.app j := ObjectProperty.homMk ((underCoconeFromRoot I s).ι.app j)
  ι.naturality _ _ f :=
    ObjectProperty.hom_ext (underCokernelNonnegativeProperty I)
      ((underCoconeFromRoot I s).ι.naturality f)

/-- Let C be abelian in object/morphism universes u,v, c a complex shape on ℤ, and I a c-shaped
complex. Let 𝒰_I be arrows I→X with cokernel terms zero in degrees n<0. For a category J in
object/morphism universes w,w' and D:J→𝒰_I, adjoin an initial index ★ to J: its carrier diagram
has value I at ★, the target X_j at j, and source arrow a_j:I→X_j on ★→j. Let J have
object/morphism universes w,w', assume C has J-colimits, and let s be a colimit cocone of this
root-adjoined carrier diagram. Write a=s_★:I→s.pt and λ_j=s_j:X_j→s.pt. The target complex of
the lifted supported cocone is exactly s.pt. The new under arrow has this carrier codomain. -/
@[simp]
theorem rootAdjoinedUnderCokernelCocone_right :
    (rootAdjoinedUnderCokernelCocone I hs).pt.obj.right = s.pt :=
  rfl

/-- Let C be abelian in object/morphism universes u,v, c a complex shape on ℤ, and I a c-shaped
complex. Let 𝒰_I be arrows I→X with cokernel terms zero in degrees n<0. For a category J in
object/morphism universes w,w' and D:J→𝒰_I, adjoin an initial index ★ to J: its carrier diagram
has value I at ★, the target X_j at j, and source arrow a_j:I→X_j on ★→j. Let J have
object/morphism universes w,w', assume C has J-colimits, and let s be a colimit cocone of this
root-adjoined carrier diagram. Write a=s_★:I→s.pt and λ_j=s_j:X_j→s.pt. The lifted supported
under arrow equals a=s_★:I→s.pt. Thus the fixed-source map is retained from the enlarged carrier
cocone. -/
@[simp]
theorem rootAdjoinedUnderCokernelCocone_hom :
    (rootAdjoinedUnderCokernelCocone I hs).pt.obj.hom = s.ι.app WithInitial.star :=
  rfl

/-- Let C be abelian in object/morphism universes u,v, c a complex shape on ℤ, and I a c-shaped
complex. Let 𝒰_I be arrows I→X with cokernel terms zero in degrees n<0. For a category J in
object/morphism universes w,w' and D:J→𝒰_I, adjoin an initial index ★ to J: its carrier diagram
has value I at ★, the target X_j at j, and source arrow a_j:I→X_j on ★→j. Let J have
object/morphism universes w,w', assume C has J-colimits, and let s be a colimit cocone of this
root-adjoined carrier diagram. Write a=s_★:I→s.pt and λ_j=s_j:X_j→s.pt. For every j∈J, the
target component of the lifted diagram leg is λ_j=s_j:X_j→s.pt. It is an under morphism because
a_j≫λ_j=a. -/
@[simp]
theorem rootAdjoinedUnderCokernelCocone_ι (j : J) :
    ((rootAdjoinedUnderCokernelCocone I hs).ι.app j).hom.right = s.ι.app (WithInitial.of j) :=
  rfl

/-- Let C be abelian in object/morphism universes u,v, c a complex shape on ℤ, and I a c-shaped
complex. Let 𝒰_I be arrows I→X with cokernel terms zero in degrees n<0. For a category J in
object/morphism universes w,w' and D:J→𝒰_I, adjoin an initial index ★ to J: its carrier diagram
has value I at ★, the target X_j at j, and source arrow a_j:I→X_j on ★→j. Let J have
object/morphism universes w,w', assume C has J-colimits, and let s be a colimit cocone of this
root-adjoined carrier diagram. Write a=s_★:I→s.pt and λ_j=s_j:X_j→s.pt. The lifted cocone of D
is colimiting in 𝒰_I. The construction uses the root-adjoined carrier universal property and
supports arbitrary diagram shapes. -/
def isColimitRootAdjoinedUnderCokernelCocone :
    IsColimit (rootAdjoinedUnderCokernelCocone I hs) :=
  isColimitOfReflects (underCokernelNonnegativeProperty I).ι (isColimitUnderCoconeFromRoot I hs)

/-- Let C be abelian in object/morphism universes u,v, c a complex shape on ℤ, and I a c-shaped
complex. Let 𝒰_I be arrows I→X with cokernel terms zero in degrees n<0. For a category J in
object/morphism universes w,w' and D:J→𝒰_I, adjoin an initial index ★ to J: its carrier diagram
has value I at ★, the target X_j at j, and source arrow a_j:I→X_j on ★→j. Let J have
object/morphism universes w,w', assume C has J-colimits, and let s be a colimit cocone of this
root-adjoined carrier diagram. Write a=s_★:I→s.pt and λ_j=s_j:X_j→s.pt. Applying the
fixed-source cokernel functor to the lifted cocone gives a colimit cocone of j↦coker(a_j), with
point coker(a). -/
def isColimitRootAdjoinedUnderCokernelReduction :
    IsColimit ((underCokernel I).mapCocone
      ((underCokernelNonnegativeProperty I).ι.mapCocone (rootAdjoinedUnderCokernelCocone I hs))) :=
  isColimitOfPreserves (underCokernel I) (isColimitUnderCoconeFromRoot I hs)

/-- Let C be abelian in object/morphism universes u,v, c a complex shape on ℤ, and I a c-shaped
complex. Let 𝒰_I be arrows I→X with cokernel terms zero in degrees n<0. For a category J in
object/morphism universes w,w' and D:J→𝒰_I, adjoin an initial index ★ to J: its carrier diagram
has value I at ★, the target X_j at j, and source arrow a_j:I→X_j on ★→j. Let J have
object/morphism universes w,w', assume C has J-colimits, and let s be a colimit cocone of this
root-adjoined carrier diagram. Write a=s_★:I→s.pt and λ_j=s_j:X_j→s.pt. For each j, if
q_j:X_j→coker(a_j) and q_a:s.pt→coker(a), then q_j≫coker(λ_j)=λ_j≫q_a. Both sides map the
carrier X_j to the cokernel of the star arrow. -/
@[reassoc]
theorem rootAdjoinedUnderCokernelCocone_π (j : J) :
    cokernel.π (D.obj j).obj.hom ≫
        (underCokernel I).map ((rootAdjoinedUnderCokernelCocone I hs).ι.app j).hom =
      s.ι.app (WithInitial.of j) ≫ cokernel.π (s.ι.app WithInitial.star) :=
  underCokernel_π_map I _

end Colimits

/-- Let C be abelian in object/morphism universes u,v, c a complex shape on ℤ, and I a c-shaped
complex. Let 𝒰_I be arrows I→X with cokernel terms zero in degrees n<0. The under object
id_I:I→I belongs to 𝒰_I: its cokernel is the zero complex, so all negative-degree terms are
zero. -/
def supportedUnderIdentity : (underCokernelNonnegativeProperty I).FullSubcategory :=
  ⟨Under.mk (𝟙 I), fun i _ => (eval C c i).map_isZero (isZero_cokernel_of_epi (𝟙 I))⟩

/-- Let C be abelian in object/morphism universes u,v, c a complex shape on ℤ, and I a c-shaped
complex. Let 𝒰_I be arrows I→X with cokernel terms zero in degrees n<0. The object id_I is
initial in 𝒰_I. For a:I→X, its unique under morphism from id_I has carrier map a:I→X. -/
def supportedUnderIdentityIsInitial : IsInitial (supportedUnderIdentity I) :=
  IsInitial.ofUniqueHom (fun X => ObjectProperty.homMk (Under.mkIdInitial.to X.obj))
    (fun X f => ObjectProperty.hom_ext (underCokernelNonnegativeProperty I)
      (Under.mkIdInitial.hom_ext f.hom (Under.mkIdInitial.to X.obj)))

/-- Let C be abelian in object/morphism universes u,v, c a complex shape on ℤ, and I a c-shaped
complex. Let 𝒰_I be arrows I→X with cokernel terms zero in degrees n<0. The binary cofan with
both inputs id_I, vertex id_I, and both legs identity is colimiting in 𝒰_I. This follows from
initiality of id_I. -/
def isColimitSupportedUnderIdentityBinaryCofan :
    IsColimit (BinaryCofan.mk (𝟙 (supportedUnderIdentity I)) (𝟙 (supportedUnderIdentity I))) where
  desc s := (supportedUnderIdentityIsInitial I).to s.pt
  fac s j := by
    rcases j with ⟨j⟩
    cases j <;> exact (supportedUnderIdentityIsInitial I).hom_ext _ _
  uniq s f _ := (supportedUnderIdentityIsInitial I).hom_ext f _

/-- Let C be abelian in object/morphism universes u,v, c a complex shape on ℤ, and I a c-shaped
complex. Let 𝒰_I be arrows I→X with cokernel terms zero in degrees n<0. If I is not a zero
complex, the target forgetful functor 𝒰_I→HomologicalComplex(C,c) does not preserve the
coproduct of id_I with itself. Its image has vertex I and two identity legs, which cannot be a
carrier coproduct when id_I≠0. -/
theorem bareUnderCokernelCarrier_not_preserves_identityPair (hI : ¬ IsZero I) :
    ¬ PreservesColimit (pair (supportedUnderIdentity I) (supportedUnderIdentity I))
      ((underCokernelNonnegativeProperty I).ι ⋙ Under.forget I) := by
  intro h
  let F := (underCokernelNonnegativeProperty I).ι ⋙ Under.forget I
  let _ : PreservesColimit (pair (supportedUnderIdentity I) (supportedUnderIdentity I)) F := h
  let D := pair (supportedUnderIdentity I) (supportedUnderIdentity I) ⋙ F
  let s : Cocone D :=
    { pt := I
      ι := Discrete.natTrans (fun j => match j with
        | ⟨WalkingPair.left⟩ => 𝟙 I
        | ⟨WalkingPair.right⟩ => 0) }
  let t := isColimitOfPreserves F (isColimitSupportedUnderIdentityBinaryCofan I)
  have hl := t.fac s ⟨WalkingPair.left⟩
  have hr := t.fac s ⟨WalkingPair.right⟩
  change 𝟙 I ≫ t.desc s = 𝟙 I at hl
  change 𝟙 I ≫ t.desc s = 0 at hr
  exact hI ((IsZero.iff_id_eq_zero _).2 (hl.symm.trans hr))

end HomologicalComplex
