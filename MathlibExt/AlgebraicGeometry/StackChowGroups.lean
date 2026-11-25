/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackCycleRelations
public import MathlibExt.AlgebraicGeometry.StackProjectiveModels
public import MathlibExt.AlgebraicGeometry.IntegerSchemeChow
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# The integral Kresch Chow carrier

The groups below are literal direct-sum quotients. The first diagram has
actual vector bundles, with transition maps prescribed by the flat pullback
along actual bundle surjections. The restricted diagram uses their actual
2-Cartesian pullbacks. The second diagram has actual projective stacks and
inclusions of components. Its stage relations are exactly the two restricted
projective pushes with equal images in the unrestricted bundle group.

No projective-bundle, homotopy, Gysin or functoriality theorem is a field of
the carrier. The normalized construction dictionaries have no opaque group
types. Their construction and the source laws are separate Wanted items.

Reference: Kresch, arXiv:math/9810166v1, Convention 2.1.1 and
Definitions 2.1.2--2.1.11. The presentation retains all geometric objects and
all arrows rather than choosing isomorphism classes. Constant-rank bundle
stages give the finite-type presentation by finite-component padding; no
cofinality statement on arbitrary stacks is claimed.

The ordinary atlas push is Mathlib's native residue-degree cycle map. Its
dictionary is completed source integration from AxiomMath/Stacks revision
c496df0d9beea9deaeabcea8492605f9a0a2313b (Apache 2.0),
StacksFrontier/AlgebraicGeometry/Chow/Vocabulary/ProperPushforward.lean.
-/

@[expose] public noncomputable section
namespace AlgebraicGeometry.StackChowGroups

open CategoryTheory CategoryTheory.Limits Opposite
open GeneralStackGeometry StackCycleGeometry StackFibreModels StackAffineModules
open StackVectorBundles StackProjectiveModels StackCycleRelations

local instance (α : Type*) : DecidableEq α := Classical.decEq α

universe u v w

/-- The additive presentation of a diagram colimit, with its literal stages. -/
def diagramRelations {I : Type u} (G : I → Type v) [∀ i, AddCommGroup (G i)]
    (A : I → I → Type w) (t : ∀ {i j}, A i j → G i →+ G j) :
    AddSubgroup (DirectSum I G) :=
  AddSubgroup.closure {z | ∃ (i j : I) (a : A i j) (x : G i),
    z = DirectSum.of G j (t a x) - DirectSum.of G i x}

abbrev AbelianColimit {I : Type u} (G : I → Type v) [∀ i, AddCommGroup (G i)]
    (A : I → I → Type w) (t : ∀ {i j}, A i j → G i →+ G j) :=
  DirectSum I G ⧸ diagramRelations G A t

def colimitClass {I : Type u} (G : I → Type v) [∀ i, AddCommGroup (G i)]
    (A : I → I → Type w) (t : ∀ {i j}, A i j → G i →+ G j) (i : I) :
    G i →+ AbelianColimit G A t :=
  (QuotientAddGroup.mk' (diagramRelations G A t)).comp (DirectSum.of G i)

variable {S : Scheme.{0}} {scope : Stack S → Prop}

/-- The normalized global square computes its actual fibre comparison. -/
structure TwoCartesianSquare {X T Y : Stack S} (f : StackHom X Y) (g : StackHom T Y) where
  apex : Stack S
  fst : StackHom apex X
  snd : StackHom apex T
  commutes : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp fst f)
    (Pseudofunctor.StrongTrans.vcomp snd g)
  cartesian : ∀ U : Over S,
    ((CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (StackCycleGeometry.component f U) (StackCycleGeometry.component g U) _).obj
      ⟨StackCycleGeometry.component fst U, StackCycleGeometry.component snd U,
        commutes.app U⟩).IsEquivalence

/-- The actual base change of a bundle: its sections are the pulled sections of `E`, linearly,
and its total space maps to that of `E` by the induced map, in a 2-Cartesian square. -/
structure BundlePullback {T X : Stack S} (p : StackHom T X) (E : VectorBundle X) where
  bundle : VectorBundle T
  rank_eq : bundle.rank = E.rank
  /-- The sections of the pulled bundle are the pulled sections of `E`, as modules. -/
  sections : bundle.module.val.presheaf ≅ pulledPresheaf p E.module.val.presheaf
  map : StackHom bundle.total E.total
  commutes : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp map E.projection)
    (Pseudofunctor.StrongTrans.vcomp bundle.projection p)
  cartesian : ∀ U : Over S,
    ((CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (StackCycleGeometry.component E.projection U) (StackCycleGeometry.component p U) _).obj
      ⟨StackCycleGeometry.component map U, StackCycleGeometry.component bundle.projection U,
        commutes.app U⟩).IsEquivalence
  /-- The total-space map is the one induced by `sections`, so it is linear on fibres: it
  preserves the zero section and cannot, for example, translate a trivial line. -/
  normalized : bundle.comparison.functor ⋙ (presheafSectionMap sections.hom).mapElements.op ⋙
      (pulledElements p E.module.val).op ≅ affineMap map ⋙ E.comparison.functor
  /-- `normalized` lies over the base 2-cell `commutes`: projected to affine points of `X` it is the
  composite of the bundles' `overBase` comparisons with the inverse of `commutes`. Without this an
  arbitrary natural isomorphism could hide a nonlinear map through stabilizers of `X`. -/
  based : ∀ b : AffinePoint bundle.total,
    (sectionForget E.module.val).map (normalized.hom.app b) =
      (affineMap p).map (bundle.overBase.hom.app b) ≫ commutes.pointInv b ≫
        E.overBase.inv.app ((affineMap map).obj b)

structure BundleStage (X : Stack S) where
  bundle : VectorBundle X
  inScope : scope bundle.total

abbrev BundleArrow {X : Stack S} (E F : BundleStage (scope := scope) X) :=
  {q : BundleMap F.bundle E.bundle // q.IsSurjective}

abbrev BundleStageGroup (D : CycleConstructionData S scope) {X : Stack S}
    (d : ℤ) (E : BundleStage (scope := scope) X) :=
  NaiveChowGroup D E.bundle.total E.inScope (d + E.bundle.rank)

/-- Regrading is literal equality of signed degrees. -/
def naiveRegrade (D : CycleConstructionData S scope) (X : Stack S) (hX : scope X)
    {a b : ℤ} (h : a = b) : NaiveChowGroup D X hX a →+ NaiveChowGroup D X hX b := by
  cases h
  exact AddMonoidHom.id _

structure BundleTransitions (D : CycleConstructionData S scope) where
  pull : ∀ (X : Stack S) (_hX : scope X) (E F : BundleStage (scope := scope) X)
    (q : BundleArrow E F), FlatPullData D F.inScope E.inScope q.val.total
      ((F.bundle.rank : ℤ) - E.bundle.rank)

def bundleTransition (D : CycleConstructionData S scope) (B : BundleTransitions D)
    {X : Stack S} (hX : scope X) (d : ℤ) {E F : BundleStage (scope := scope) X}
    (q : BundleArrow E F) : BundleStageGroup D d E →+ BundleStageGroup D d F :=
  (naiveRegrade D F.bundle.total F.inScope (by omega)).comp
    ((B.pull X hX E F q).onChow (d + E.bundle.rank))

abbrev BundleChowGroup (D : CycleConstructionData S scope) (B : BundleTransitions D)
    (X : Stack S) (hX : scope X) (d : ℤ) :=
  AbelianColimit (BundleStageGroup D d) BundleArrow (bundleTransition D B hX d)

def bundleClass (D : CycleConstructionData S scope) (B : BundleTransitions D)
    (X : Stack S) (hX : scope X) (d : ℤ) (E : BundleStage (scope := scope) X) :
    BundleStageGroup D d E →+ BundleChowGroup D B X hX d :=
  colimitClass (BundleStageGroup D d) BundleArrow (bundleTransition D B hX d) E

structure RestrictedBundleSystem (D : CycleConstructionData S scope) where
  pullback : ∀ (T X : Stack S) (_hT : scope T) (_hX : scope X)
    (p : StackHom T X) (E : BundleStage (scope := scope) X), BundlePullback p E.bundle
  inScope : ∀ (T X : Stack S) (hT : scope T) (hX : scope X)
    (p : StackHom T X) (E : BundleStage (scope := scope) X),
    scope (pullback T X hT hX p E).bundle.total
  map : ∀ (T X : Stack S) (hT : scope T) (hX : scope X)
    (p : StackHom T X) (E F : BundleStage (scope := scope) X) (_q : BundleArrow E F),
    BundleMap (pullback T X hT hX p F).bundle (pullback T X hT hX p E).bundle
  surjective : ∀ (T X : Stack S) (hT : scope T) (hX : scope X)
    (p : StackHom T X) (E F : BundleStage (scope := scope) X) (q : BundleArrow E F),
    (map T X hT hX p E F q).IsSurjective
  normalized : ∀ (T X : Stack S) (hT : scope T) (hX : scope X)
    (p : StackHom T X) (E F : BundleStage (scope := scope) X) (q : BundleArrow E F),
    StackVectorBundles.TwoIso
      (Pseudofunctor.StrongTrans.vcomp (map T X hT hX p E F q).total
        (pullback T X hT hX p E).map)
      (Pseudofunctor.StrongTrans.vcomp (pullback T X hT hX p F).map q.val.total)

def pulledStage {D : CycleConstructionData S scope} (R : RestrictedBundleSystem D)
    {T X : Stack S} (hT : scope T) (hX : scope X) (p : StackHom T X)
    (E : BundleStage (scope := scope) X) : BundleStage (scope := scope) T :=
  ⟨(R.pullback T X hT hX p E).bundle, R.inScope T X hT hX p E⟩

abbrev RestrictedStageGroup (D : CycleConstructionData S scope) (R : RestrictedBundleSystem D)
    {T X : Stack S} (hT : scope T) (hX : scope X) (p : StackHom T X) (d : ℤ)
    (E : BundleStage (scope := scope) X) := BundleStageGroup D d (pulledStage R hT hX p E)

def restrictedTransition (D : CycleConstructionData S scope) (B : BundleTransitions D)
    (R : RestrictedBundleSystem D) {T X : Stack S} (hT : scope T) (hX : scope X)
    (p : StackHom T X) (d : ℤ) {E F : BundleStage (scope := scope) X}
    (q : BundleArrow E F) :
    RestrictedStageGroup D R hT hX p d E →+ RestrictedStageGroup D R hT hX p d F :=
  bundleTransition D B hT d
    ⟨R.map T X hT hX p E F q, R.surjective T X hT hX p E F q⟩

abbrev RestrictedBundleChowGroup (D : CycleConstructionData S scope) (B : BundleTransitions D)
    (R : RestrictedBundleSystem D) {T X : Stack S} (hT : scope T) (hX : scope X)
    (p : StackHom T X) (d : ℤ) :=
  AbelianColimit (RestrictedStageGroup D R hT hX p d) BundleArrow
    (restrictedTransition D B R hT hX p d)

def restrictedClass (D : CycleConstructionData S scope) (B : BundleTransitions D)
    (R : RestrictedBundleSystem D) {T X : Stack S} (hT : scope T) (hX : scope X)
    (p : StackHom T X) (d : ℤ) (E : BundleStage (scope := scope) X) :
    RestrictedStageGroup D R hT hX p d E →+
      RestrictedBundleChowGroup D B R hT hX p d :=
  colimitClass _ BundleArrow (restrictedTransition D B R hT hX p d) E

structure RestrictedComparison (D : CycleConstructionData S scope) (B : BundleTransitions D)
    (R : RestrictedBundleSystem D) where
  iota : ∀ (T X : Stack S) (hT : scope T) (hX : scope X) (p : StackHom T X) (d : ℤ),
    RestrictedBundleChowGroup D B R hT hX p d →+ BundleChowGroup D B T hT d
  normalized : ∀ (T X : Stack S) (hT : scope T) (hX : scope X) (p : StackHom T X)
    (d : ℤ) (E : BundleStage (scope := scope) X) (a : RestrictedStageGroup D R hT hX p d E),
    iota T X hT hX p d (restrictedClass D B R hT hX p d E a) =
      bundleClass D B T hT d (pulledStage R hT hX p E) a

/-- An actual projective base change of the target atlas. -/
structure ProjectiveAtlasLift {T X : Stack S} (p : StackHom T X) (a : CycleAtlas X) where
  atlas : CycleAtlas T
  map : atlas.atlas.U ⟶ a.atlas.U
  pointIso : (StackCycleGeometry.component p atlas.atlas.U).obj atlas.atlas.point ≅
    (pull X map).obj a.atlas.point
  /-- The displayed square is 2-Cartesian: its own object of the fibre category (the atlas point
  of `T` over `map`, with `pointIso`) is terminal, so the atlas of `T` represents the fibre of `p`
  over the atlas of `X` through this square (a nontrivial étale self-cover of it does not). -/
  universal : IsTerminal (CostructuredArrow.mk (S := totalMap p) (T := point a.atlas.U a.atlas.point)
    (Y := point atlas.atlas.U atlas.atlas.point)
    (⟨map, pointIso.hom⟩ : (totalMap p).obj (point atlas.atlas.U atlas.atlas.point) ⟶
      point a.atlas.U a.atlas.point))
  rank_eq : atlas.relativeRank = a.relativeRank

structure NaiveProjectivePushData (D : CycleConstructionData S scope) {T X : Stack S}
    (hT : scope T) (hX : scope X) (p : StackHom T X) where
  atlas : ∀ a : CycleAtlas X, ProjectiveAtlasLift p a
  cycle : ∀ d : ℤ, CycleGroup T d →+ CycleGroup X d
  normalized : ∀ (d : ℤ) (c : CycleGroup T d) (a : CycleAtlas X),
    atlasPull (D.principal X hX).geometry a d (cycle d c) =
      AlgebraicCycle.map (atlas a).map.left Order.height Order.height
        (atlasPull (D.principal T hT).geometry (atlas a).atlas d c)
  descends : ∀ (d : ℤ) (c : CycleGroup T d), c ∈ rationalRelations D T hT d →
    cycle d c ∈ rationalRelations D X hX d

def NaiveProjectivePushData.onChow {D : CycleConstructionData S scope} {T X : Stack S}
    {hT : scope T} {hX : scope X} {p : StackHom T X}
    (P : NaiveProjectivePushData D hT hX p) (d : ℤ) :
    NaiveChowGroup D T hT d →+ NaiveChowGroup D X hX d :=
  QuotientAddGroup.map _ _ (P.cycle d) (P.descends d)

structure RestrictedProjectiveSystem (D : CycleConstructionData S scope)
    (B : BundleTransitions D) (R : RestrictedBundleSystem D) where
  stage : ∀ (T X : Stack S) (hT : scope T) (hX : scope X) (p : StackHom T X)
    (_projective : ProjectiveMorphism p) (E : BundleStage (scope := scope) X),
    NaiveProjectivePushData D (R.inScope T X hT hX p E) E.inScope
      (R.pullback T X hT hX p E).map
  push : ∀ (T X : Stack S) (hT : scope T) (hX : scope X) (p : StackHom T X)
    (_projective : ProjectiveMorphism p) (d : ℤ),
    RestrictedBundleChowGroup D B R hT hX p d →+ BundleChowGroup D B X hX d
  normalized : ∀ (T X : Stack S) (hT : scope T) (hX : scope X) (p : StackHom T X)
    (projective : ProjectiveMorphism p) (d : ℤ) (E : BundleStage (scope := scope) X)
    (a : RestrictedStageGroup D R hT hX p d E),
    push T X hT hX p projective d (restrictedClass D B R hT hX p d E a) =
      bundleClass D B X hX d E
        (naiveRegrade D E.bundle.total E.inScope
          (by rw [(R.pullback T X hT hX p E).rank_eq])
          ((stage T X hT hX p projective E).onChow
            (d + (R.pullback T X hT hX p E).bundle.rank) a))

def IsProjectiveRelation (D : CycleConstructionData S scope) (B : BundleTransitions D)
    (R : RestrictedBundleSystem D) (I : RestrictedComparison D B R)
    (P : RestrictedProjectiveSystem D B R) {X Y : Stack S}
    (hX : scope X) (f : StackHom X Y) (d : ℤ) (z : BundleChowGroup D B X hX d) : Prop :=
  ∃ (T : Stack S) (hT : scope T) (p₁ p₂ : StackHom T X)
      (hp₁ : ProjectiveMorphism p₁) (hp₂ : ProjectiveMorphism p₂)
      (β₁ : RestrictedBundleChowGroup D B R hT hX p₁ d)
      (β₂ : RestrictedBundleChowGroup D B R hT hX p₂ d),
    Nonempty (StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp p₁ f)
      (Pseudofunctor.StrongTrans.vcomp p₂ f)) ∧
    I.iota T X hT hX p₁ d β₁ = I.iota T X hT hX p₂ d β₂ ∧
    z = P.push T X hT hX p₂ hp₂ d β₂ - P.push T X hT hX p₁ hp₁ d β₁

def projectiveRelations (D : CycleConstructionData S scope) (B : BundleTransitions D)
    (R : RestrictedBundleSystem D) (I : RestrictedComparison D B R)
    (P : RestrictedProjectiveSystem D B R) {X Y : Stack S} (hX : scope X)
    (f : StackHom X Y) (d : ℤ) : AddSubgroup (BundleChowGroup D B X hX d) :=
  AddSubgroup.closure {z | IsProjectiveRelation D B R I P hX f d z}

structure ProjectiveStage (Y : Stack S) where
  source : Stack S
  inScope : scope source
  map : StackHom source Y
  projective : ProjectiveMorphism map

/-- On finite-type stacks an open and closed immersion is an inclusion of
a union of connected components; all scheme fibres are the actual fibres. -/
structure ComponentInclusion {X Y : Stack S} (f : StackHom X Y) where
  fibres : ∀ (T : Over S) (y : Y.Fibre T), SchemeFibreModel f T y
  openImmersion : ∀ (T : Over S) (y : Y.Fibre T), IsOpenImmersion (fibres T y).scheme.hom
  closedImmersion : ∀ (T : Over S) (y : Y.Fibre T), IsClosedImmersion (fibres T y).scheme.hom

structure ProjectiveArrow {Y : Stack S} (A A' : ProjectiveStage (scope := scope) Y) where
  map : StackHom A.source A'.source
  inclusion : ComponentInclusion map
  projective : ProjectiveMorphism map
  overBase : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp map A'.map) A.map

structure ComponentTransitions (D : CycleConstructionData S scope) (B : BundleTransitions D)
    (R : RestrictedBundleSystem D) (I : RestrictedComparison D B R)
    (P : RestrictedProjectiveSystem D B R) where
  push : ∀ (Y : Stack S) (A A' : ProjectiveStage (scope := scope) Y)
    (_g : ProjectiveArrow A A') (d : ℤ),
    BundleChowGroup D B A.source A.inScope d →+ BundleChowGroup D B A'.source A'.inScope d
  normalized : ∀ (Y : Stack S) (A A' : ProjectiveStage (scope := scope) Y)
    (g : ProjectiveArrow A A') (d : ℤ)
    (β : RestrictedBundleChowGroup D B R A.inScope A'.inScope g.map d),
    push Y A A' g d (I.iota A.source A'.source A.inScope A'.inScope g.map d β) =
      P.push A.source A'.source A.inScope A'.inScope g.map g.projective d β
  /-- Every bundle class on `A` is restricted along the component inclusion (pad a bundle stage
  by a trivial bundle on the other components), so `normalized` determines `push` on all classes
  and the colimit does not depend on the provider. -/
  restricted_surjective : ∀ (Y : Stack S) (A A' : ProjectiveStage (scope := scope) Y)
    (g : ProjectiveArrow A A') (d : ℤ),
    Function.Surjective (I.iota A.source A'.source A.inScope A'.inScope g.map d)
  descends : ∀ (Y : Stack S) (A A' : ProjectiveStage (scope := scope) Y)
    (g : ProjectiveArrow A A') (d : ℤ) (z : BundleChowGroup D B A.source A.inScope d),
    z ∈ projectiveRelations D B R I P A.inScope A.map d →
      push Y A A' g d z ∈ projectiveRelations D B R I P A'.inScope A'.map d

/-- The component push is determined by the restricted projective pushes. -/
theorem ComponentTransitions.push_eq_of_iota {D : CycleConstructionData S scope}
    {B : BundleTransitions D} {R : RestrictedBundleSystem D} {I : RestrictedComparison D B R}
    {P : RestrictedProjectiveSystem D B R} (C C' : ComponentTransitions D B R I P) (Y : Stack S)
    (A A' : ProjectiveStage (scope := scope) Y) (g : ProjectiveArrow A A') (d : ℤ) :
    C.push Y A A' g d = C'.push Y A A' g d := by
  refine AddMonoidHom.ext fun z ↦ ?_
  obtain ⟨β, rfl⟩ := C.restricted_surjective Y A A' g d z
  rw [C.normalized, C'.normalized]

structure KreschPresentation (D : CycleConstructionData S scope) where
  bundle : BundleTransitions D
  restricted : RestrictedBundleSystem D
  comparison : RestrictedComparison D bundle restricted
  projective : RestrictedProjectiveSystem D bundle restricted
  components : ComponentTransitions D bundle restricted comparison projective

abbrev ProjectiveStageGroup (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {Y : Stack S} (d : ℤ) (A : ProjectiveStage (scope := scope) Y) :=
  BundleChowGroup D K.bundle A.source A.inScope d ⧸
    projectiveRelations D K.bundle K.restricted K.comparison K.projective A.inScope A.map d

def projectiveTransition (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {Y : Stack S} (d : ℤ) {A A' : ProjectiveStage (scope := scope) Y}
    (g : ProjectiveArrow A A') : ProjectiveStageGroup D K d A →+ ProjectiveStageGroup D K d A' :=
  QuotientAddGroup.map _ _ (K.components.push Y A A' g d) (K.components.descends Y A A' g d)

/-- Kresch's integral group, not the naive rational-equivalence quotient. -/
abbrev ChowGroup (D : CycleConstructionData S scope) (K : KreschPresentation D)
    (Y : Stack S) (_hY : scope Y) (d : ℤ) :=
  AbelianColimit (ProjectiveStageGroup D K (Y := Y) d) ProjectiveArrow
    (projectiveTransition D K d)

def projectiveClass (D : CycleConstructionData S scope) (K : KreschPresentation D)
    (Y : Stack S) (hY : scope Y) (d : ℤ) (A : ProjectiveStage (scope := scope) Y) :
    BundleChowGroup D K.bundle A.source A.inScope d →+ ChowGroup D K Y hY d :=
  (colimitClass (ProjectiveStageGroup D K d) ProjectiveArrow (projectiveTransition D K d) A).comp
    (QuotientAddGroup.mk' _)

/-- Manolache's coefficients are rational; the underlying Kresch carrier is integral. -/
abbrev RationalChowGroup (D : CycleConstructionData S scope) (K : KreschPresentation D)
    (Y : Stack S) (hY : scope Y) (d : ℤ) := TensorProduct ℤ ℚ (ChowGroup D K Y hY d)

structure CycleClassData (D : CycleConstructionData S scope) (K : KreschPresentation D)
    (X : Stack S) (hX : scope X) where
  zero : BundleStage (scope := scope) X
  rank_zero : zero.bundle.rank = 0
  pull : FlatPullData D zero.inScope hX zero.bundle.projection 0
  identity : ProjectiveMorphism (Pseudofunctor.StrongTrans.id X.toPseudofunctor)

def naiveToBundle (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {X : Stack S} {hX : scope X} (C : CycleClassData D K X hX) (d : ℤ) :
    NaiveChowGroup D X hX d →+ BundleChowGroup D K.bundle X hX d :=
  (bundleClass D K.bundle X hX d C.zero).comp
    ((naiveRegrade D C.zero.bundle.total C.zero.inScope (by simp [C.rank_zero])).comp
      (C.pull.onChow d))

def stackCycleClass (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {X : Stack S} {hX : scope X} (C : CycleClassData D K X hX) (d : ℤ) :
    CycleGroup X d →+ ChowGroup D K X hX d :=
  (projectiveClass D K X hX d ⟨X, hX, _, C.identity⟩).comp
    ((naiveToBundle D K C d).comp (naiveCycleClass D X hX d))

def chowRegrade (D : CycleConstructionData S scope) (K : KreschPresentation D)
    (X : Stack S) (hX : scope X) {a b : ℤ} (h : a = b) :
    ChowGroup D K X hX a →+ ChowGroup D K X hX b := by
  cases h
  exact AddMonoidHom.id _

/-- Every irreducible component of every actual scheme fibre has dimension n. -/
def PureSchemeRelativeDimension {X Y : Scheme.{0}} (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∀ (y : Y) (Z : irreducibleComponents (f.fiber y)),
    topologicalKrullDim Z = (n : ℕ)

/-- Flatness and signed relative dimension on actual stack base changes.
The atlas rank is measured by its smooth scheme charts. -/
structure FlatMorphism {X Y : Stack S} (f : StackHom X Y) (shift : ℤ) where
  fibres : ∀ (T : Over S) (y : Y.Fibre T), StackFibreModel f T y
  atlas : ∀ (T : Over S) (y : Y.Fibre T), (fibres T y).stack.SmoothAtlas
  rank : ∀ (T : Over S) (_y : Y.Fibre T), ℕ
  rank_normalized : ∀ (T : Over S) (y : Y.Fibre T)
    (U : Over T.left) (x : (fibres T y).stack.Fibre U),
    ∃ c : ((atlas T y).baseChange U x).Chart, SmoothOfRelativeDimension (rank T y) c.map
  flat : ∀ (T : Over S) (y : Y.Fibre T), Flat (atlas T y).U.hom
  pure : ∀ (T : Over S) (y : Y.Fibre T), ∃ n : ℕ,
    (n : ℤ) = shift + rank T y ∧ PureSchemeRelativeDimension (atlas T y).U.hom n

structure BundleFlatPullData (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {X Y : Stack S} (hX : scope X) (hY : scope Y) (f : StackHom X Y) (shift : ℤ) where
  stage : ∀ E : BundleStage (scope := scope) Y,
    FlatPullData D (K.restricted.inScope X Y hX hY f E) E.inScope
      (K.restricted.pullback X Y hX hY f E).map shift
  map : ∀ d : ℤ, BundleChowGroup D K.bundle Y hY d →+
    BundleChowGroup D K.bundle X hX (d + shift)
  normalized : ∀ (d : ℤ) (E : BundleStage (scope := scope) Y) (a : BundleStageGroup D d E),
    map d (bundleClass D K.bundle Y hY d E a) =
      bundleClass D K.bundle X hX (d + shift) (pulledStage K.restricted hX hY f E)
        (naiveRegrade D (K.restricted.pullback X Y hX hY f E).bundle.total
          (K.restricted.inScope X Y hX hY f E)
          (by dsimp [pulledStage]; rw [(K.restricted.pullback X Y hX hY f E).rank_eq]; omega)
          ((stage E).onChow (d + E.bundle.rank) a))

/-- Flat pullback is fixed on every projective representative by the
actual 2-Cartesian square and the atlas-normalized bundle-stage pullback. -/
structure FlatChowPullData (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {X Y : Stack S} (hX : scope X) (hY : scope Y) (f : StackHom X Y) (shift : ℤ) where
  flat : FlatMorphism f shift
  square : ∀ A : ProjectiveStage (scope := scope) Y, TwoCartesianSquare A.map f
  inScope : ∀ A : ProjectiveStage (scope := scope) Y, scope (square A).apex
  projective : ∀ A : ProjectiveStage (scope := scope) Y, ProjectiveMorphism (square A).snd
  bundlePull : ∀ A : ProjectiveStage (scope := scope) Y,
    BundleFlatPullData D K (inScope A) A.inScope (square A).fst shift
  map : ∀ d : ℤ, ChowGroup D K Y hY d →+ ChowGroup D K X hX (d + shift)
  normalized : ∀ (d : ℤ) (A : ProjectiveStage (scope := scope) Y)
    (a : BundleChowGroup D K.bundle A.source A.inScope d),
    map d (projectiveClass D K Y hY d A a) =
      projectiveClass D K X hX (d + shift)
        ⟨(square A).apex, inScope A, (square A).snd, projective A⟩ ((bundlePull A).map d a)

/-- Pushforward is fixed on all projective representatives by composition
of their actual projective maps. Functoriality is a separate theorem. -/
structure ProjectiveChowPushData (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {X Y : Stack S} (hX : scope X) (hY : scope Y) (f : StackHom X Y) where
  projective : ProjectiveMorphism f
  composite : ∀ A : ProjectiveStage (scope := scope) X,
    ProjectiveMorphism (Pseudofunctor.StrongTrans.vcomp A.map f)
  map : ∀ d : ℤ, ChowGroup D K X hX d →+ ChowGroup D K Y hY d
  normalized : ∀ (d : ℤ) (A : ProjectiveStage (scope := scope) X)
    (a : BundleChowGroup D K.bundle A.source A.inScope d),
    map d (projectiveClass D K X hX d A a) =
      projectiveClass D K Y hY d
        ⟨A.source, A.inScope, Pseudofunctor.StrongTrans.vcomp A.map f, composite A⟩ a

/-- A scheme dictionary retains the entire actual fibred category and
fixes every integral cut by literal factorization through its subscheme. -/
structure SchemeCycleDictionary {k : Type} [Field k]
    (U : IntegerSchemeChow.FieldScheme k) (X : Stack (Spec (.of k))) where
  comparison : Total X ≌ Over U.scheme.left
  overBase : comparison.functor ⋙ Over.map U.scheme.hom ≅
    Pseudofunctor.CoGrothendieck.forget X.toPseudofunctor
  closed : ∀ (d : ℤ) (_Z : IntegralClosedSubstack X d),
    IntegerSchemeChow.ClosedIntegralScheme U.scheme.left d
  normalized : ∀ (d : ℤ) (Z : IntegralClosedSubstack X d)
    (T : Over (Spec (.of k))) (x : X.Fibre T),
    Z.val.predicate T x ↔ ∃ b : (comparison.functor.obj (point T x)).left ⟶ (closed d Z).scheme,
      b ≫ (closed d Z).inclusion = (comparison.functor.obj (point T x)).hom

def schemeCycleMap {k : Type} [Field k] {U : IntegerSchemeChow.FieldScheme k}
    {X : Stack (Spec (.of k))} (C : SchemeCycleDictionary U X) (d : ℤ) :
    CycleGroup X d →+ IntegerSchemeChow.CycleGroup U.scheme.left d :=
  FreeAbelianGroup.lift (fun Z => IntegerSchemeChow.closedCycle (C.closed d Z))

structure SchemeComparisonData {k : Type} [Field k]
    (D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)) (K : KreschPresentation D)
    (U : IntegerSchemeChow.FieldScheme k) (X : Stack (Spec (.of k))) (hX : FiniteTypeArtin k X)
    (C : SchemeCycleDictionary U X) (classes : CycleClassData D K X hX) where
  map : ∀ d : ℤ, ChowGroup D K X hX d →+ IntegerSchemeChow.ChowGroup U d
  normalized : ∀ (d : ℤ) (z : CycleGroup X d),
    map d (stackCycleClass D K classes d z) =
      IntegerSchemeChow.cycleClass U d (schemeCycleMap C d z)

structure FundamentalCycleData (D : CycleConstructionData S scope) (X : Stack S)
    (hX : scope X) (d : ℤ) where
  cycle : CycleGroup X d
  normalized : ∀ a : CycleAtlas X,
    atlasPull (D.principal X hX).geometry a d cycle = integralFundamentalCycle a.atlas.U.left

def rationalMap {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) :
    TensorProduct ℤ ℚ A →ₗ[ℚ] TensorProduct ℤ ℚ B :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : ℚ →ₗ[ℚ] ℚ) f.toIntLinearMap

def rationalCycleClass (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {X : Stack S} {hX : scope X} (C : CycleClassData D K X hX) (d : ℤ) :
    CycleGroup X d →+ RationalChowGroup D K X hX d :=
  ((TensorProduct.mk ℤ ℚ (ChowGroup D K X hX d) 1).toAddMonoidHom).comp
    (stackCycleClass D K C d)

/-- An open full cut has actual open scheme fibres and a normalized fppf
realization, just as the closed-cut cycle carrier does. -/
structure OpenSubstack (X : Stack S) where
  predicate : ∀ T : Over S, X.Fibre T → Prop
  pull_mem : ∀ {T V : Over S} (a : V ⟶ T) (x : X.Fibre T),
    predicate T x → predicate V ((pull X a).obj x)
  iso_mem : ∀ (T : Over S) (x y : X.Fibre T), Nonempty (x ≅ y) →
    (predicate T x ↔ predicate T y)
  represented : ∀ (T : Over S) (x : X.Fibre T), ∃ U : Over T.left,
    IsOpenImmersion U.hom ∧ ∀ (V : Over S) (a : V ⟶ T),
      predicate V ((pull X a).obj x) ↔ ∃ b : V.left ⟶ U.left, b ≫ U.hom = a.left
  realization : ∃ (Y : Stack S) (f : StackHom Y X),
    Nonempty (∀ T : Over S, (StackCycleGeometry.component f T).FullyFaithful) ∧
    ∀ (T : Over S) (x : X.Fibre T), predicate T x ↔
      ∃ y : Y.Fibre T, Nonempty ((StackCycleGeometry.component f T).obj y ≅ x)

def OpenSubstack.source {X : Stack S} (U : OpenSubstack X) : Stack S :=
  Classical.choose U.realization

def OpenSubstack.inclusion {X : Stack S} (U : OpenSubstack X) : StackHom U.source X :=
  Classical.choose (Classical.choose_spec U.realization)

structure OpenClosedComplement {X : Stack S} (Z : ClosedSubstack X) (U : OpenSubstack X) where
  normalized : ∀ (T : Over S) (x : X.Fibre T) (V : Over S) (a : V ⟶ T),
    U.predicate V ((pull X a).obj x) ↔
      ∀ (W : Over S) (b : W ⟶ V), IsEmpty W.left ∨
        ¬ Z.predicate W ((pull X (b ≫ a)).obj x)

structure FiniteFieldExtension (k : Type) [Field k] where
  field : Type
  [isField : Field field]
  embedding : k →+* field
  finite : letI := embedding.toAlgebra
    FiniteDimensional k field

attribute [instance] FiniteFieldExtension.isField

/-- Geometric surjectivity: actual field-valued objects lift after a
finite extension of their given residue field. -/
def SurjectiveOnFieldPoints {X Y : Stack S} (f : StackHom X Y) : Prop :=
  ∀ (k : Type) [Field k] (q : Spec (.of k) ⟶ S) (y : Y.Fibre (Over.mk q)),
    ∃ (L : FiniteFieldExtension k)
      (x : X.Fibre (Over.mk (Spec.map (CommRingCat.ofHom L.embedding) ≫ q))),
      Nonempty ((StackCycleGeometry.component f
        (Over.mk (Spec.map (CommRingCat.ofHom L.embedding) ≫ q))).obj x ≅
          (pull Y (Over.homMk (Spec.map (CommRingCat.ofHom L.embedding)) rfl)).obj y)

structure RationalChowCover (D : CycleConstructionData S scope) (K : KreschPresentation D)
    (X : Stack S) (hX : scope X) where
  stage : ProjectiveStage (scope := scope) X
  surjective : SurjectiveOnFieldPoints stage.map
  chowSurjective : ∀ d : ℤ, Function.Surjective
    (rationalMap (projectiveClass D K X hX d stage))

/-- A proper DM morphism presented by a projective Chow cover whose
composite is projective. This records the actual geometric cover used for
rational descent, including its cycle-class map, rather than an arbitrary push. -/
structure DMProperModel (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {X Y : Stack S} (hX : scope X) (hY : scope Y) (f : StackHom X Y) where
  sourceDM : X.IsDeligneMumfordStack
  targetDM : Y.IsDeligneMumfordStack
  cover : RationalChowCover D K X hX
  composite : ProjectiveMorphism (Pseudofunctor.StrongTrans.vcomp cover.stage.map f)

structure RationalPushData (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {X Y : Stack S} (hX : scope X) (hY : scope Y) (f : StackHom X Y)
    (M : DMProperModel D K hX hY f) where
  map : ∀ d : ℤ, RationalChowGroup D K X hX d →ₗ[ℚ] RationalChowGroup D K Y hY d
  normalized : ∀ (d : ℤ) (a : TensorProduct ℤ ℚ
    (BundleChowGroup D K.bundle M.cover.stage.source M.cover.stage.inScope d)),
    map d (rationalMap (projectiveClass D K X hX d M.cover.stage) a) =
      rationalMap (projectiveClass D K Y hY d
        ⟨M.cover.stage.source, M.cover.stage.inScope,
          Pseudofunctor.StrongTrans.vcomp M.cover.stage.map f, M.composite⟩) a

def rationalDegree {A : Type*} [AddCommGroup A] (degree : A →+ ℤ) :
    TensorProduct ℤ ℚ A →ₗ[ℚ] ℚ :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.smulRight (LinearMap.id : ℚ →ₗ[ℚ] ℚ)
      ((Int.castAddHom ℚ).comp degree).toIntLinearMap)

def schemeStackDegree {k : Type} [Field k]
    {D : CycleConstructionData (Spec (.of k)) (FiniteTypeArtin k)} {K : KreschPresentation D}
    {U : IntegerSchemeChow.FieldScheme k} [IsProper U.scheme.hom]
    {X : Stack (Spec (.of k))} {hX : FiniteTypeArtin k X} {C : SchemeCycleDictionary U X}
    {classes : CycleClassData D K X hX} (comparison : SchemeComparisonData D K U X hX C classes)
    (degree : IntegerSchemeChow.DegreeComparison U) : RationalChowGroup D K X hX 0 →ₗ[ℚ] ℚ :=
  rationalDegree (degree.degree.comp (comparison.map 0))

end AlgebraicGeometry.StackChowGroups
