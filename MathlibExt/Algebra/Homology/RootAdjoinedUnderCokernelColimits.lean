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
# Root-adjoined carrier colimits for the nonnegative under-cokernel category

For any diagram of under arrows with supported cokernel, adjoining the common
source computes its actual colimit on carriers. The colimit's star leg is the
new under arrow and the other legs are the original carrier cocone legs.
For a nonzero source the bare carrier functor fails to preserve even the
binary coproduct of the supported identity arrow with itself.
-/

@[expose] public section

noncomputable section

universe v u w w'

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] {c : ComplexShape ℤ}
variable (I : HomologicalComplex C c)
variable {J : Type w} [Category.{w'} J]

/-- Adjoin the fixed source as the star of the native carrier diagram; each star
arrow is the actual under arrow. -/
abbrev rootAdjoinedUnderCokernelDiagram
    (D : J ⥤ (underCokernelNonnegativeProperty I).FullSubcategory) :
    WithInitial J ⥤ HomologicalComplex C c :=
  WithInitial.liftFromUnder.obj (D ⋙ (underCokernelNonnegativeProperty I).ι)

/-- The native under cocone recovered from the carriers and their star leg. -/
abbrev underCoconeFromRoot {D : J ⥤ (underCokernelNonnegativeProperty I).FullSubcategory}
    (s : Cocone (rootAdjoinedUnderCokernelDiagram I D)) :
    Cocone (D ⋙ (underCokernelNonnegativeProperty I).ι) :=
  WithInitial.coconeEquiv.inverse.obj s

/-- A colimiting rooted carrier cocone has the original under-object universal property. -/
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

/-- Lift a colimit of the root-adjoined carriers to the support category, using
the landed fixed-source cokernel support theorem on the genuine under cocone. -/
def rootAdjoinedUnderCokernelCocone : Cocone D where
  pt := ⟨(underCoconeFromRoot I s).pt,
    underCokernelNonnegativeProperty_of_isColimit I
    (isColimitUnderCoconeFromRoot I hs) (fun j => (D.obj j).property)⟩
  ι.app j := ObjectProperty.homMk ((underCoconeFromRoot I s).ι.app j)
  ι.naturality _ _ f :=
    ObjectProperty.hom_ext (underCokernelNonnegativeProperty I)
      ((underCoconeFromRoot I s).ι.naturality f)

/-- The lifted colimit has the supplied carrier point. -/
@[simp]
theorem rootAdjoinedUnderCokernelCocone_right :
    (rootAdjoinedUnderCokernelCocone I hs).pt.obj.right = s.pt :=
  rfl

/-- The fixed source arrow in the lift is exactly the original star leg. -/
@[simp]
theorem rootAdjoinedUnderCokernelCocone_hom :
    (rootAdjoinedUnderCokernelCocone I hs).pt.obj.hom = s.ι.app WithInitial.star :=
  rfl

/-- Each lifted diagram leg has exactly the supplied original carrier component. -/
@[simp]
theorem rootAdjoinedUnderCokernelCocone_ι (j : J) :
    ((rootAdjoinedUnderCokernelCocone I hs).ι.app j).hom.right = s.ι.app (WithInitial.of j) :=
  rfl

/-- The lift is colimiting for the original diagram, including empty and
disconnected shapes. -/
def isColimitRootAdjoinedUnderCokernelCocone :
    IsColimit (rootAdjoinedUnderCokernelCocone I hs) :=
  isColimitOfReflects (underCokernelNonnegativeProperty I).ι (isColimitUnderCoconeFromRoot I hs)

/-- The cokernel of the star arrow is a colimit of the literal original reductions. -/
def isColimitRootAdjoinedUnderCokernelReduction :
    IsColimit ((underCokernel I).mapCocone
      ((underCokernelNonnegativeProperty I).ι.mapCocone (rootAdjoinedUnderCokernelCocone I hs))) :=
  isColimitOfPreserves (underCokernel I) (isColimitUnderCoconeFromRoot I hs)

/-- The colimit on actual reductions uses the same carrier legs and the original
cokernel projections. -/
@[reassoc]
theorem rootAdjoinedUnderCokernelCocone_π (j : J) :
    cokernel.π (D.obj j).obj.hom ≫
        (underCokernel I).map ((rootAdjoinedUnderCokernelCocone I hs).ι.app j).hom =
      s.ι.app (WithInitial.of j) ≫ cokernel.π (s.ι.app WithInitial.star) :=
  underCokernel_π_map I _

end Colimits

/-- The identity under arrow belongs to the support category for any fixed
source, since its actual cokernel is zero. -/
def supportedUnderIdentity : (underCokernelNonnegativeProperty I).FullSubcategory :=
  ⟨Under.mk (𝟙 I), fun i _ => (eval C c i).map_isZero (isZero_cokernel_of_epi (𝟙 I))⟩

/-- The supported identity arrow is the actual initial object under the fixed source. -/
def supportedUnderIdentityIsInitial : IsInitial (supportedUnderIdentity I) :=
  IsInitial.ofUniqueHom (fun X => ObjectProperty.homMk (Under.mkIdInitial.to X.obj))
    (fun X f => ObjectProperty.hom_ext (underCokernelNonnegativeProperty I)
      (Under.mkIdInitial.hom_ext f.hom (Under.mkIdInitial.to X.obj)))

/-- In the support category the binary coproduct of two identity arrows again
has the identity vertex and both identity legs. -/
def isColimitSupportedUnderIdentityBinaryCofan :
    IsColimit (BinaryCofan.mk (𝟙 (supportedUnderIdentity I)) (𝟙 (supportedUnderIdentity I))) where
  desc s := (supportedUnderIdentityIsInitial I).to s.pt
  fac s j := by
    rcases j with ⟨j⟩
    cases j <;> exact (supportedUnderIdentityIsInitial I).hom_ext _ _
  uniq s f _ := (supportedUnderIdentityIsInitial I).hom_ext f _

/-- At a nonzero source, forgetting the source arrow fails to preserve the
binary coproduct of two copies of the supported identity arrow. -/
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
