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
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Mathlib.CategoryTheory.Abelian.CommSq
public import MathlibExt.CategoryTheory.Limits.Constructions.Under.ConnectedCocone

/-!
# Connected colimits of carriers with nonnegative reductions

Let C be abelian and I a ℤ-indexed cochain complex. The nonnegative reduced-carrier category
consists of arrows a:I→X whose cokernel has zero terms below degree zero. Its carrier functor U
forgets a and retains X.

For a nonempty connected diagram, a carrier cocone with legs λ_j determines one common source
arrow a=a_j≫λ_j. When C has colimits of the diagram shape and that carrier cocone is colimiting,
it lifts to a colimit in the reduced-carrier category with the same target and legs. Thus U
creates these connected colimits.

For a span in this category whose carrier square is a pullback over a common target, with one
target map mono, the pushout comparison into the common target is mono on carriers. The
statement uses the entire cochain complexes and their carrier intersection.
-/

@[expose] public section

noncomputable section

universe v u w w'

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] (I : CochainComplex C ℤ)

/-- Let C be abelian in object/morphism universes u,v and I a ℤ-indexed cochain complex in C. Let
𝒰_I be the full category of arrows a:I→X whose cokernel complexes have zero terms in degrees
n<0, and U(a)=X. An object is its source arrow a:I→X together with the condition that (coker
a)_n is zero for every n<0. Morphisms X→Y commute with the given arrows from I. -/
abbrev NonnegativeReducedCarrier :=
  (underCokernelNonnegativeProperty I).FullSubcategory

/-- Let C be abelian in object/morphism universes u,v and I a ℤ-indexed cochain complex in C. Let
𝒰_I be the full category of arrows a:I→X whose cokernel complexes have zero terms in degrees
n<0, and U(a)=X. The functor U:𝒰_I→CochainComplex(C,ℤ) sends a:I→X to X and an under-arrow
morphism to its map of target complexes. -/
abbrev nonnegativeReducedCarrierForget : NonnegativeReducedCarrier I ⥤ CochainComplex C ℤ :=
  (underCokernelNonnegativeProperty I).ι ⋙ Under.forget I

section Connected

variable {J : Type w} [Category.{w'} J] [IsConnected J]

/-- Let C be abelian in object/morphism universes u,v and I a ℤ-indexed cochain complex in C. Let
𝒰_I be the full category of arrows a:I→X whose cokernel complexes have zero terms in degrees
n<0, and U(a)=X. For a nonempty connected J and D:J→Under(I), any cocone of its target complexes
with legs λ_j lifts to a cocone in Under(I). Its vertex is a:I→s.pt, where a=a_j≫λ_j for every
j. Connectedness makes these composites equal. -/
def liftConnectedUnderCarrierCocone {D : J ⥤ Under I}
    (s : Cocone (D ⋙ Under.forget I)) : Cocone D :=
  liftConnectedUnderCocone I s

variable [HasColimitsOfShape J C]

/-- Let C be abelian in object/morphism universes u,v and I a ℤ-indexed cochain complex in C. Let
𝒰_I be the full category of arrows a:I→X whose cokernel complexes have zero terms in degrees
n<0, and U(a)=X. Let J be a nonempty connected category in independent object/morphism universes
w,w', and suppose C has J-colimits. For D:J→𝒰_I and a colimit carrier cocone s of U∘D, the lift
has target s.pt, source arrow a=a_j≫s_j, and the same carrier legs s_j. Its cokernel is
nonnegative by colimit preservation of the fixed-source cokernel functor. -/
def liftNonnegativeReducedCarrierCocone {D : J ⥤ NonnegativeReducedCarrier I}
    {s : Cocone (D ⋙ nonnegativeReducedCarrierForget I)} (hs : IsColimit s) : Cocone D := by
  let t := liftConnectedUnderCarrierCocone I (D := D ⋙ (underCokernelNonnegativeProperty I).ι) s
  have ht : IsColimit t := isColimitOfReflects (Under.forget I) (by exact hs)
  exact
    { pt := ⟨t.pt, underCokernelNonnegativeProperty_of_isColimit I ht fun j => (D.obj j).property⟩
      ι.app j := ObjectProperty.homMk (t.ι.app j)
      ι.naturality _ _ f :=
        ObjectProperty.hom_ext (underCokernelNonnegativeProperty I) (t.ι.naturality f) }

/-- Let C be abelian in object/morphism universes u,v and I a ℤ-indexed cochain complex in C. Let
𝒰_I be the full category of arrows a:I→X whose cokernel complexes have zero terms in degrees
n<0, and U(a)=X. Let J be a nonempty connected category in independent object/morphism universes
w,w', and suppose C has J-colimits. For a colimiting cocone s of U∘D, applying U to its lifted
cocone gives s itself, with the same target complex and every leg. -/
@[simp]
theorem mapCocone_liftNonnegativeReducedCarrierCocone {D : J ⥤ NonnegativeReducedCarrier I}
    {s : Cocone (D ⋙ nonnegativeReducedCarrierForget I)} (hs : IsColimit s) :
    (nonnegativeReducedCarrierForget I).mapCocone (liftNonnegativeReducedCarrierCocone I hs) = s :=
  rfl

/-- Let C be abelian in object/morphism universes u,v and I a ℤ-indexed cochain complex in C. Let
𝒰_I be the full category of arrows a:I→X whose cokernel complexes have zero terms in degrees
n<0, and U(a)=X. Let J be a nonempty connected category in independent object/morphism universes
w,w', and suppose C has J-colimits. For D:J→𝒰_I, colimit carrier cocone s, and j∈J, one has
a_j≫s_j=a, where a:I→s.pt is the source arrow of the lifted cocone. -/
@[reassoc]
theorem comp_ι_eq_liftNonnegativeReducedCarrierCocone_hom
    {D : J ⥤ NonnegativeReducedCarrier I}
    {s : Cocone (D ⋙ nonnegativeReducedCarrierForget I)} (hs : IsColimit s) (j : J) :
    (D.obj j).obj.hom ≫ s.ι.app j = (liftNonnegativeReducedCarrierCocone I hs).pt.obj.hom :=
  Under.w ((liftNonnegativeReducedCarrierCocone I hs).ι.app j).hom

/-- Let C be abelian in object/morphism universes u,v and I a ℤ-indexed cochain complex in C. Let
𝒰_I be the full category of arrows a:I→X whose cokernel complexes have zero terms in degrees
n<0, and U(a)=X. Let J be a nonempty connected category in independent object/morphism universes
w,w', and suppose C has J-colimits. If s is colimiting for U∘D, the lifted cocone of D is
colimiting in 𝒰_I. Its universal morphisms preserve the common source arrow. -/
def isColimitLiftNonnegativeReducedCarrierCocone {D : J ⥤ NonnegativeReducedCarrier I}
    {s : Cocone (D ⋙ nonnegativeReducedCarrierForget I)} (hs : IsColimit s) :
    IsColimit (liftNonnegativeReducedCarrierCocone I hs) :=
  isColimitOfReflects (underCokernelNonnegativeProperty I).ι
    (isColimitOfReflects (Under.forget I) hs)

/-- Let C be abelian in object/morphism universes u,v and I a ℤ-indexed cochain complex in C. Let
𝒰_I be the full category of arrows a:I→X whose cokernel complexes have zero terms in degrees
n<0, and U(a)=X. Let J be a nonempty connected category in independent object/morphism universes
w,w', and suppose C has J-colimits. The functor U creates J-colimits: each colimiting carrier
cocone lifts to a colimiting supported under cocone with the same target and legs. -/
instance nonnegativeReducedCarrierForgetCreatesColimitsOfShape :
    CreatesColimitsOfShape J (nonnegativeReducedCarrierForget I) where
  CreatesColimit := createsColimitOfReflectsIso fun _ hs =>
    { liftedCocone := liftNonnegativeReducedCarrierCocone I hs
      validLift := eqToIso (mapCocone_liftNonnegativeReducedCarrierCocone I hs)
      makesColimit := isColimitLiftNonnegativeReducedCarrierCocone I hs }

/-- Let C be abelian in object/morphism universes u,v and I a ℤ-indexed cochain complex in C. Let
𝒰_I be the full category of arrows a:I→X whose cokernel complexes have zero terms in degrees
n<0, and U(a)=X. Let J be a nonempty connected category in independent object/morphism universes
w,w', and suppose C has J-colimits. The category 𝒰_I has colimits of shape J. They are obtained
by taking carrier colimits and lifting the common source arrow and cokernel support. -/
instance nonnegativeReducedCarrier_hasColimitsOfShape :
    HasColimitsOfShape J (NonnegativeReducedCarrier I) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape
    (nonnegativeReducedCarrierForget I)

end Connected

/-- Let C be abelian in object/morphism universes u,v and I a ℤ-indexed cochain complex in C. Let
𝒰_I be the full category of arrows a:I→X whose cokernel complexes have zero terms in degrees
n<0, and U(a)=X. For a commuting square t:L→A,l:L→B,a:A→D,b:B→D in 𝒰_I with t≫a=l≫b, assume
(U(t),U(l),U(a),U(b)) is a pullback square and U(a) is mono. Then U(pushout.desc(a,b)) is mono
as a map from the carrier pushout to U(D). -/
theorem nonnegativeReducedCarrier_pushoutDesc_mono
    {L A B D : NonnegativeReducedCarrier I} {t : L ⟶ A} {l : L ⟶ B}
    {a : A ⟶ D} {b : B ⟶ D} (w : t ≫ a = l ≫ b)
    (h : IsPullback ((nonnegativeReducedCarrierForget I).map t)
      ((nonnegativeReducedCarrierForget I).map l)
      ((nonnegativeReducedCarrierForget I).map a)
      ((nonnegativeReducedCarrierForget I).map b))
    [Mono ((nonnegativeReducedCarrierForget I).map a)] :
    Mono ((nonnegativeReducedCarrierForget I).map (pushout.desc a b w)) := by
  let F := nonnegativeReducedCarrierForget I
  have hp := (IsPushout.of_hasPushout t l).map F
  refine hp.mono_of_isPullback_of_mono h (F.map (pushout.desc a b w)) ?_ ?_
  · rw [← F.map_comp, pushout.inl_desc]
  · rw [← F.map_comp, pushout.inr_desc]

end CochainComplex
