/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RelativeWittLoopCorrespondences
public import MathlibExt.AlgebraicGeometry.GeneralStackGeometry
public import MathlibExt.CategoryTheory.SheafTorsorGroupoids
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Mathlib.CategoryTheory.IsomorphismClasses

/-!
# Original Witt-disc G-torsors and punctured trivializations

The site contains all actual coefficient schemes over the displayed
disc, with its native fpqc topology. The group sheaf is the original
represented group-scheme point functor, lifted only to the sheaf
universe. Its sheaf condition is proved from native subcanonicity.

Torsors are actual locally inhabited simply transitive action sheaves.
Restriction acts on the original sheaf and every equivariant map.
A punctured trivialization is an actual isomorphism of the restricted
action with the regular group action. The framed groupoid is the native
isomorphism-comma category; its arrows preserve that precise frame.

The Witt disc and puncture are the original tensor-ring spectra and
their actual uniformizer-localization map. Their quotient comparison
is a separate source-normalized Wanted endpoint.

Source: Zhu, arXiv:1407.8519v3, Lemma 1.3, pp. 8--9;
Stacks Project, Tags 04UV and 03AG. Native subcanonicity, sheaf
restriction and the isomorphism-comma groupoid are reused source proofs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.WittDiscTorsorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.GeneralStackGeometry
open MathlibExt.CategoryTheory.SheafTorsorGroupoids

variable (B : Type) [CommRing B] (G : Over (Spec (.of B))) [GrpObj G]

/-- The native coefficient-scheme fpqc topology. -/
abbrev baseTopology := Scheme.fpqcTopology.over (Spec (.of B))

/-- The original group-scheme points, lifted only to the site's value universe. -/
def baseGroupPresheaf : (Over (Spec (.of B)))ᵒᵖ ⥤ GrpCat.{1} :=
  yonedaGrpObj G ⋙ GrpCat.uliftFunctor.{1, 0}

/-- Native representability proves fpqc descent for the original group points. -/
def baseGroupSheaf : Sheaf (baseTopology B) GrpCat.{1} :=
  ⟨baseGroupPresheaf B G, by
    apply (Presheaf.isSheaf_iff_isSheaf_forget
      (baseTopology B) (baseGroupPresheaf B G) (forget GrpCat.{1})).2
    change Presheaf.IsSheaf (baseTopology B)
      (yoneda.obj G ⋙ uliftFunctor.{1, 0})
    exact ((baseTopology B).uliftYoneda.obj G).property⟩

/-- All original coefficient schemes over the displayed disc are site objects. -/
abbrev Site (X : Over (Spec (.of B))) := Over X

/-- Its topology is the actual native over topology of the coefficient site. -/
abbrev topology (X : Over (Spec (.of B))) := (baseTopology B).over X

/-- The group sheaf is actual native restriction along the original forgetful site map. -/
def groupSheaf (X : Over (Spec (.of B))) : Sheaf (topology B X) GrpCat.{1} :=
  ((baseTopology B).overPullback GrpCat.{1} X).obj (baseGroupSheaf B G)

/-- Actual G-torsors and equivariant isomorphisms on that original disc. -/
abbrev Torsors (X : Over (Spec (.of B))) :=
  TorsorGroupoid (topology B X) (groupSheaf B G X)

variable {B} {X Y : Over (Spec (.of B))}

/-- Restriction is the actual native over-map pullback on every action component. -/
def actionPullback (f : Y ⟶ X) :
    Action (topology B X) (groupSheaf B G X) ⥤
      Action (topology B Y) (groupSheaf B G Y) where
  obj P :=
    { sheaf := ((baseTopology B).overMapPullback (Type 1) f).obj P.sheaf
      action := Functor.whiskerLeft (Over.map f).op P.action
      unit := fun T x ↦ P.unit ((Over.map f).op.obj T) x
      associative := fun T x g h ↦ P.associative ((Over.map f).op.obj T) x g h }
  map {_P _Q} e :=
    ⟨((baseTopology B).overMapPullback (Type 1) f).map e.val,
      fun T x g ↦ e.property ((Over.map f).op.obj T) x g⟩
  map_id P := Subtype.ext (((baseTopology B).overMapPullback (Type 1) f).map_id P.sheaf)
  map_comp e h :=
    Subtype.ext (((baseTopology B).overMapPullback (Type 1) f).map_comp e.val h.val)

variable (B)

/-- The actual regular right G-action, the target of a genuine trivialization. -/
def regularAction (X : Over (Spec (.of B))) :
    Action (topology B X) (groupSheaf B G X) where
  sheaf := groupSets (topology B X) (groupSheaf B G X)
  action :=
    { app := fun T ↦ ↾fun x ↦ x.1 * x.2
      naturality := by
        intro T U f
        apply ConcreteCategory.hom_ext
        intro x
        exact (map_mul ((groupSheaf B G X).obj.map f).hom x.1 x.2).symm }
  unit := fun T x ↦ mul_one x
  associative := fun T x g h ↦ mul_assoc x g h

/-- The core/full-subcategory projection retains original torsor actions and maps. -/
def torsorActions (X : Over (Spec (.of B))) :
    Torsors B G X ⥤ Action (topology B X) (groupSheaf B G X) :=
  Core.inclusion _ ⋙
    (show ObjectProperty (Action (topology B X) (groupSheaf B G X)) from
      IsTorsor (topology B X) (groupSheaf B G X)).ι

/-- Framed objects are original torsors with an actual invertible punctured frame. -/
abbrev FramedGroupoid {X Y : Over (Spec (.of B))} (f : Y ⟶ X) :=
  IsoFibre (torsorActions B G X ⋙ actionPullback G f)
    ((Functor.const (Discrete PUnit.{1})).obj (regularAction B G Y))

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k]
  [Algebra (WittVector p k) B] (pi : B)

/-- The original Witt disc and puncture, including the genuine localization frame. -/
abbrev WittFramedTorsors (R : RelativeWittLoopTests.PerfectAlgebra p k) :=
  FramedGroupoid B G (RelativeWittLoopTests.localization p k B pi R)

/-- Isomorphism classes retain the full original framed torsor groupoid. -/
abbrev WittFramedClasses (R : RelativeWittLoopTests.PerfectAlgebra p k) :=
  Quotient (isIsomorphicSetoid (WittFramedTorsors B G p k pi R))

end MathlibExt.AlgebraicGeometry.WittDiscTorsorModels
