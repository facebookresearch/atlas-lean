/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AnalyticBundleModifications
public import MathlibExt.AlgebraicGeometry.UntiltingCartierModels
public import MathlibExt.AlgebraicGeometry.AlgebraicGroupPointRepresentations

/-!
# Original torsor coordinates near an analytic Cartier divisor

A pole chart is an actual affinoid etale neighbourhood. Both its
divisor and its puncture are the actual pullback diagrams. Its parameter
generates the original kernel ideal on every restricted open and is
regular on every stalk. Integral frames are actual equivariant
trivializations of the two original G-torsors on that neighbourhood.

The comparison element below evaluates the original punctured
isomorphism between those two frames. The comparison is transported
only through the displayed native pullback square; it is not a freely
selected element of G of a period ring.

Reference: Fargues--Scholze, arXiv:2102.13459v4, Section III.3, p. 97,
and Section VI.1. No meromorphic extension or completion is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AnalyticMeromorphicCoordinates

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite Topology
open _root_.AlgebraicGeometry
open AnalyticTateAdicModels AnalyticDiamondEtaleSites AnalyticGroupTorsorSites
open AnalyticTorsorPullbacks AnalyticBundlePrestackModels AnalyticBundleModifications
open MathlibExt.CategoryTheory.SheafTorsorGroupoids

variable (p : ℕ) [Fact p.Prime] (E : Type) [Field E]

/-- The original global analytic section ring. -/
abbrev SectionRing (V : ESpace p E) := V.left.obj.space.presheaf.obj (op ⊤)

/-- Restriction is the original analytic morphism on that complete section ring. -/
def sectionMap {V W : ESpace p E} (f : W ⟶ V) :
    SectionRing p E V →+* SectionRing p E W :=
  ((globalRings p).map f.left.op).hom

variable (G : Over (Spec (.of E))) [GrpObj G]
  (H : ∀ V : ESpace p E, GroupDescent p E G V)
  (P : PullbackPreservation p E G H)

variable {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)

/-- The original closed-map kernel, for either characteristic of the coefficient field. -/
def divisorKernel {V W : ESpace p E} (f : W ⟶ V)
    (Z : TopologicalSpace.Opens V.left.obj.space) :
    Ideal (V.left.obj.space.presheaf.obj (op Z)) :=
  RingHom.ker (f.left.hom.val.c.app (op Z)).hom

/-- A genuine affinoid neighbourhood of the original Cartier divisor. -/
structure PoleChart where
  space : ESpace p E
  pair : TatePair p
  model : AffinoidModel p pair
  model_same : space.left.obj = model.valued
  map : space ⟶ X
  etale : IsAnalyticEtale p map.left
  divisor : ESpace p E
  divisorMap : divisor ⟶ space
  divisorToOriginal : divisor ⟶ D
  divisorSquare : IsPullback divisorMap divisorToOriginal map d
  puncture : Puncture p E divisorMap
  punctureToOriginal : puncture.space ⟶ U.space
  punctureSquare : IsPullback puncture.map punctureToOriginal map U.map
  parameter : SectionRing p E space
  regular : ∀ x : space.left.obj.space,
    IsRegular (space.left.obj.space.presheaf.germ ⊤ x (by trivial) parameter)
  ideal : ∀ V : TopologicalSpace.Opens space.left.obj.space,
    divisorKernel p E divisorMap V = Ideal.span
      {space.left.obj.space.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op parameter}

/-- A closed Cartier divisor with a genuine affinoid etale pole-chart cover. -/
structure CartierAtlas where
  closed : IsClosedEmbedding d.left.hom.val.base
  stalk_surjective : ∀ x, Function.Surjective (d.left.hom.val.stalkMap x)
  index : Type 1
  chart : index → PoleChart p E d U
  covers : ∀ x : D.left.obj.space, ∃ i,
    d.left.hom.val.base x ∈ Set.range (chart i).map.left.hom.val.base

/-- Forget to the actual torsor action, retaining each original equivariant map. -/
def bundleActions (V : ESpace p E) : Bundles p E G H V ⥤
    Action (topology p E V) (groupSheaf p E G V (H V)) :=
  Core.inclusion _ ⋙
    (show ObjectProperty (Action (topology p E V) (groupSheaf p E G V (H V))) from
      IsTorsor (topology p E V) (groupSheaf p E G V (H V))).ι

/-- The actual regular group action, with its original sectionwise multiplication. -/
def regularAction (V : ESpace p E) :
    Action (topology p E V) (groupSheaf p E G V (H V)) where
  sheaf := groupSets (topology p E V) (groupSheaf p E G V (H V))
  action :=
    { app := fun T ↦ TypeCat.ofHom (fun x ↦ x.1 * x.2)
      naturality := by
        intro T W f
        apply ConcreteCategory.hom_ext
        intro x
        exact (map_mul ((groupSheaf p E G V (H V)).obj.map f).hom x.1 x.2).symm }
  unit := fun _ x ↦ mul_one x
  associative := fun _ x a b ↦ mul_assoc x a b

variable (Q : PoleChart p E d U)

/-- An integral frame trivializes the actual restricted analytic torsor. -/
abbrev IntegralFrame (B : Bundles p E G H X) :=
  (actionPullback p E G Q.map (H X) (H Q.space)).obj
    ((bundleActions p E G H X).obj B) ≅ regularAction p E G H Q.space

omit [Fact p.Prime] in
/-- The two source test objects are equal by the actual puncture pullback square. -/
theorem puncture_test_equality :
    (Over.mk (Q.puncture.map ≫ Q.map) : Site p E X) =
      Over.mk (Q.punctureToOriginal ≫ U.map) :=
  congrArg Over.mk Q.punctureSquare.w

variable (M : Modification p E G H P d U)
  (left : IntegralFrame p E G H d U Q M.left)
  (right : IntegralFrame p E G H d U Q M.right)

omit [Fact p.Prime] in
/-- The native comparison square on every actual refinement of the punctured test. -/
theorem refined_puncture_test_equality (T : Site p E Q.puncture.space) :
    (Over.mk ((T.hom ≫ Q.puncture.map) ≫ Q.map) : Site p E X) =
      Over.mk ((T.hom ≫ Q.punctureToOriginal) ≫ U.map) := by
  apply congrArg Over.mk
  rw [Category.assoc, Category.assoc, Q.punctureSquare.w]

/-- Evaluate the original punctured isomorphism on every original refined test point. -/
def comparisonValue (T : Site p E Q.puncture.space)
    (a : (pointGroups p E G).obj (op T.left)) :
    (pointGroups p E G).obj (op T.left) := by
  let localTest : Site p E Q.space := Over.mk (T.hom ≫ Q.puncture.map)
  let originalTest : Site p E U.space := Over.mk (T.hom ≫ Q.punctureToOriginal)
  let e := refined_puncture_test_equality p E d U Q T
  let before := (left.inv.val.hom.app (op localTest))
    a
  let transported := ((forgetBundles p E G H X).obj M.left).obj.map
    (eqToHom e.symm).op before
  let compared := ((forgetBundles p E G H U.space).map M.punctured.hom).hom.app
    (op originalTest) transported
  let returned := ((forgetBundles p E G H X).obj M.right).obj.map
    (eqToHom e).op compared
  exact (right.hom.val.hom.app (op localTest)) returned

/-- The actual group element is the value at one in the original identity punctured test. -/
def comparisonElement : (pointGroups p E G).obj (op Q.puncture.space) :=
  comparisonValue p E G H P d U Q M left right (Over.mk (𝟙 Q.puncture.space)) 1

/-- The coefficient algebra is the actual punctured analytic section ring over original E. -/
def puncturedCoefficientTest : CommAlgCat.{0} E := by
  let f : E →+* SectionRing p E Q.puncture.space := coefficients p E Q.puncture.space
  letI := f.toAlgebra
  exact CommAlgCat.of E (SectionRing p E Q.puncture.space)

/-- Evaluate any original representation on that exact comparison element. -/
def comparisonMatrix (n : ℕ)
    (ρ : AlgebraicGroupPointRepresentations.Representation E G n) :
    Matrix (Fin n) (Fin n) (SectionRing p E Q.puncture.space) :=
  AlgebraicGroupPointRepresentations.actionMatrix E G n ρ
    (puncturedCoefficientTest p E d U Q)
    (comparisonElement p E G H P d U Q M left right)

end MathlibExt.AlgebraicGeometry.AnalyticMeromorphicCoordinates
