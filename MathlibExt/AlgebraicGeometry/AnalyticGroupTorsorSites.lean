/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites
public import MathlibExt.CategoryTheory.SheafTorsorGroupoids
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Actual analytic coefficient spaces and G-torsor sites

An E-space is a native costructured arrow: an actual analytic Tate-adic
space and its scalar map E -> Gamma(X,O_X). Morphisms are precisely
the original analytic maps which preserve those scalars. The scalar map is an abstract ring map:
this is a site of algebraically decorated analytic spaces, not in general the site of analytic
spaces over `Spa(E, E⁺)` (for a topological field base, continuity of the scalar map and
integrality of the image of `E⁺` are additional conditions, imposed by applications that need
that site). The test
scheme is literally Spec of its native global section ring over E.
The group presheaf evaluates the actual native group scheme on that
test, with every original restriction map.

The big etale site has all actual E-spaces over X and jointly
surjective analytic-etale covering maps. This allows restriction along
the native composition functor Over(Y) -> Over(X), without assuming
that an arbitrary object map to X is etale. G-torsors are actual action
sheaves, locally inhabited and simply transitive, with equivariant maps.

Sources: Fargues--Scholze, arXiv:2102.13459v4, Definitions I.2.4/III.1.1;
Stacks Project, Tags 04UV and 03AG.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticGroupTorsorSites

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open AnalyticTateAdicModels AnalyticDiamondEtaleSites

variable (p : ℕ) [Fact p.Prime] (E : Type) [CommRing E]

/-- The original analytic-space forgetful functor, retaining actual valued maps. -/
def locallyRingedSpaces : AnalyticAdicSpace p ⥤ LocallyRingedSpace :=
  (show ObjectProperty ValuedSpace from HasAnalyticAtlas p).ι ⋙ forgetValuations

/-- Global sections are the native locally ringed space Gamma functor. -/
def globalRings : (AnalyticAdicSpace p)ᵒᵖ ⥤ CommRingCat :=
  (locallyRingedSpaces p).op ⋙ LocallyRingedSpace.Γ

abbrev ESpace := CostructuredArrow (globalRings p).rightOp (op (CommRingCat.of E))

def forgetSpaces : ESpace p E ⥤ AnalyticAdicSpace p :=
  CostructuredArrow.proj _ _

def coefficients (X : ESpace p E) : E →+* (globalRings p).obj (op X.left) := X.hom.unop.hom

/-- Every analytic object is tested by its actual affine global-ring scheme. -/
def affineTests : ESpace p E ⥤ Over (Spec (.of E)) where
  obj X := Over.mk (Spec.map X.hom.unop)
  map {X Y} f := Over.homMk (Spec.map ((globalRings p).map f.left.op)) (by
    change Spec.map ((globalRings p).map f.left.op) ≫ Spec.map Y.hom.unop = Spec.map X.hom.unop
    rw [← Spec.map_comp]
    exact congrArg Spec.map (congrArg Quiver.Hom.unop f.w))
  map_id X := by
    apply Over.OverMorphism.ext
    change Spec.map ((globalRings p).map (𝟙 X.left).op) = 𝟙 _
    change Spec.map ((globalRings p).map (𝟙 (op X.left))) = 𝟙 _
    rw [_root_.CategoryTheory.Functor.map_id]
    exact Spec.map_id _
  map_comp {X Y Z} f g := by
    apply Over.OverMorphism.ext
    change Spec.map ((globalRings p).map (f.left ≫ g.left).op) =
      Spec.map ((globalRings p).map f.left.op) ≫ Spec.map ((globalRings p).map g.left.op)
    rw [op_comp, _root_.CategoryTheory.Functor.map_comp, Spec.map_comp]

variable (G : Over (Spec (.of E))) [GrpObj G]

def pointGroups : (ESpace p E)ᵒᵖ ⥤ GrpCat := (affineTests p E).op ⋙ yonedaGrpObj G

abbrev Site (X : ESpace p E) := Over X

/-- Etale maps are tested on their actual Tate-ring charts and all original points. -/
def ambientTopology : GrothendieckTopology (ESpace p E) :=
  sInf {J | ∀ (I : Type 1) (T : ESpace p E) (U : I → ESpace p E) (f : ∀ i, U i ⟶ T),
    (∀ i, IsAnalyticEtale p (f i).left) →
    (∀ x : T.left.obj.space,
      ∃ i, x ∈ Set.range (f i).left.hom.val.base) → Sieve.ofArrows U f ∈ J T}

/-- The big etale topology is the native Over topology of that exact original site. -/
def topology (X : ESpace p E) : GrothendieckTopology (Site p E X) :=
  (ambientTopology p E).over X

def groupPresheaf (X : ESpace p E) : (Site p E X)ᵒᵖ ⥤ GrpCat :=
  (Over.forget X).op ⋙ pointGroups p E G

def GroupDescent (X : ESpace p E) : Prop :=
  Presheaf.IsSheaf (topology p E X) (groupPresheaf p E G X)

def groupSheaf (X : ESpace p E) (H : GroupDescent p E G X) :
    Sheaf (topology p E X) GrpCat := ⟨groupPresheaf p E G X, H⟩

abbrev Torsors (X : ESpace p E) (H : GroupDescent p E G X) :=
  MathlibExt.CategoryTheory.SheafTorsorGroupoids.TorsorGroupoid
    (topology p E X) (groupSheaf p E G X H)

/-- Pullback on the big site is the actual native composition functor. -/
def pullbackSite {X Y : ESpace p E} (f : Y ⟶ X) : Site p E Y ⥤ Site p E X := Over.map f

omit [Fact p.Prime] in
theorem pullback_groupPresheaf {X Y : ESpace p E} (f : Y ⟶ X) :
    (pullbackSite p E f).op ⋙ groupPresheaf p E G X = groupPresheaf p E G Y := rfl

end MathlibExt.AlgebraicGeometry.AnalyticGroupTorsorSites
