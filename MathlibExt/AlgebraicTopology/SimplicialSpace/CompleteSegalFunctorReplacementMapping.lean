/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.FirstProjectionFunctorReplacementComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorCoreMapping

/-!
# The same derived mapping interpretation for every allowed first-JT source

The proved weak core map is localized using the supplied source replacement.
The original CSS power core identifies the same original one-fold Q/R end.
The characteristic triangles compare any two allowed source choices through
that actual power core, preserving their original maps and factor choices.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MonoidalClosed Opposite
open scoped MonoidalCategory SimplicialSpace.Cartesian SSet.modelCategoryQuillen
open SimplicialPresheaf.OriginalLocalDerived

namespace SimplicialSpace.FirstProjection

private abbrev H : SSet.{u} ⥤ SSet.realizationWeakEquivalences.{u}.Localization :=
  SSet.realizationWeakEquivalences.Q
private local instance sourceLocallySmall : LocallySmall.{u} (CategoryTheory.FinitePowerSite.Source 1) :=
  @CategoryTheory.locallySmall_of_univLE _ _ UnivLE.zero

private abbrev F := SimplicialPresheaf.OrderedJFS.originalFamily.{u} 1

/-- Localize the exact weak core comparison of the supplied first-JT source replacement. -/
def replacementCoreIso (W V : SimplicialSpace.{u}) (Q : SSet.{u}) (q : Q ⟶ right.obj W)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) (hq : SSet.categoricalEquivalences q) :
    H.{u}.obj (SSet.coreFunctor.obj (right.obj ((ihom W).obj V))) ≅
      H.{u}.obj (SSet.coreFunctor.obj ((ihom Q).obj (right.obj V))) := by
  let _ : IsIso (H.{u}.map (SSet.coreFunctor.map (replacementComparison W V Q q))) :=
    Localization.inverts H.{u} SSet.realizationWeakEquivalences _
      (replacementComparison_coreWeak W V Q q hW hV hq)
  exact asIso (H.{u}.map (SSet.coreFunctor.map (replacementComparison W V Q q)))

/-- Every allowed native source has the same original one-fold Q/R-derived-end interpretation. -/
def replacementCoreMappingIso (W V : SimplicialSpace.{u}) (Q : SSet.{u}) (q : Q ⟶ right.obj W)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) (hq : SSet.categoricalEquivalences q) :
    H.{u}.obj (SSet.coreFunctor.obj ((ihom Q).obj (right.obj V))) ≅
      H.{u}.obj (((localDerivedEnd F.{u}).obj (op (originalImage W))).obj (originalImage V)) :=
  (replacementCoreIso W V Q q hW hV hq).symm ≪≫ cssPowerCoreMappingIso W V hV

/-- Its triangle retains the exact supplied core map and the same original power-core interpretation. -/
theorem replacementCoreMappingIso_triangle (W V : SimplicialSpace.{u}) (Q : SSet.{u})
    (q : Q ⟶ right.obj W) (hW : completeSegalSpaces W) (hV : completeSegalSpaces V)
    (hq : SSet.categoricalEquivalences q) :
    (replacementCoreIso W V Q q hW hV hq).hom ≫ (replacementCoreMappingIso W V Q q hW hV hq).hom =
      (cssPowerCoreMappingIso W V hV).hom := by
  change (replacementCoreIso W V Q q hW hV hq).hom ≫
    ((replacementCoreIso W V Q q hW hV hq).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]

/-- Two allowed first-JT source replacements are compared by their two actual core maps. -/
def replacementSourceChange (W V : SimplicialSpace.{u}) {Q P : SSet.{u}}
    (q : Q ⟶ right.obj W) (p : P ⟶ right.obj W)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V)
    (hq : SSet.categoricalEquivalences q) (hp : SSet.categoricalEquivalences p) :
    H.{u}.obj (SSet.coreFunctor.obj ((ihom Q).obj (right.obj V))) ≅
      H.{u}.obj (SSet.coreFunctor.obj ((ihom P).obj (right.obj V))) :=
  (replacementCoreIso W V Q q hW hV hq).symm ≪≫ replacementCoreIso W V P p hW hV hp

/-- The source-choice comparison retains both supplied maps from the same CSS power core. -/
theorem replacementSourceChange_triangle (W V : SimplicialSpace.{u}) {Q P : SSet.{u}}
    (q : Q ⟶ right.obj W) (p : P ⟶ right.obj W)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V)
    (hq : SSet.categoricalEquivalences q) (hp : SSet.categoricalEquivalences p) :
    (replacementCoreIso W V Q q hW hV hq).hom ≫ (replacementSourceChange W V q p hW hV hq hp).hom =
      (replacementCoreIso W V P p hW hV hp).hom := by
  change (replacementCoreIso W V Q q hW hV hq).hom ≫
    ((replacementCoreIso W V Q q hW hV hq).inv ≫ _) = _
  rw [Iso.hom_inv_id_assoc]

/-- Allowed source choices preserve precisely the same derived-end interpretation. -/
theorem replacementSourceChange_mapping (W V : SimplicialSpace.{u}) {Q P : SSet.{u}}
    (q : Q ⟶ right.obj W) (p : P ⟶ right.obj W)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V)
    (hq : SSet.categoricalEquivalences q) (hp : SSet.categoricalEquivalences p) :
    (replacementSourceChange W V q p hW hV hq hp).hom ≫
        (replacementCoreMappingIso W V P p hW hV hp).hom =
      (replacementCoreMappingIso W V Q q hW hV hq).hom := by
  apply (cancel_epi (replacementCoreIso W V Q q hW hV hq).hom).mp
  rw [← Category.assoc, replacementSourceChange_triangle, replacementCoreMappingIso_triangle,
    replacementCoreMappingIso_triangle]

end SimplicialSpace.FirstProjection
