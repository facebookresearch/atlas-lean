/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The correspondence action and projector-realization interfaces follow
AxiomMath/Stacks, revision c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/WeilCohomology/Concrete/RealizationFunctor.lean
and StacksFrontier/AlgebraicGeometry/WeilCohomology/Motives/ChowGroups.lean,
licensed under Apache 2.0. Modification notice: use the geometric-family
rational quotient and the actual rational sheaf Betti cup/pull/Gysin maps;
prove the conditional category, linear functors and literal projector-range
construction here. The existing abstract Chow/calculus/Karoubi results are
not asserted to be missing, and no general arithmetic realization is claimed.
-/

module
public import MathlibExt.AlgebraicGeometry.BettiCycleRealization
public import MathlibExt.AlgebraicGeometry.BettiGysin
public import MathlibExt.CategoryTheory.LinearKaroubi
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
/-!
# Betti realization of actual rational correspondences and projectors

Degree-zero morphisms X → Y are the actual rational CH_(dim Y)(X × Y), so
their classes have cohomological degree 2 dim X. The constructed action is
pr₂,*(cl(α) cup pr₁* a), with the degree transported explicitly. Composition
is characterized on actual smooth transverse proper presentations by the
literal scheme-theoretic middle fibre product and its pushed fundamental
cycle. Its compatible global construction remains a Wanted input.

Given that characterized calculus, the rational category, effective Karoubi
motives, linear Betti functor and projector-range functor are completed.
The projector carrier is exactly the range of the constructed Betti action.
The Künneth map is also the actual finite sum of tensor products of pulled
classes and cup product; its bijectivity is requested separately.

References: Fulton, *Intersection Theory*, §16.1 and §19.1; Stacks Tags
0FG0 and 0FHL. Tate inversion, mixed motives and arithmetic comparison are
not claimed by this effective complex Betti packet.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.BettiMotiveRealization
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Idempotents
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open PerverseSheaves ComplexAnalytification GeometricChow
open BettiRealization CompactSupportBetti ProperBettiFunctoriality BettiFunctoriality BettiGysin
open _root_.MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted
  (IsProjectiveOverC)
attribute [local instance] HasDerivedCategory.standard

structure SmoothObject where
  scheme : PerverseSheaves.ComplexScheme
  dimension : ℕ
  [variety : IsComplexVariety scheme]
  [smooth : SmoothOfRelativeDimension dimension scheme.hom]
  [proper : IsProper scheme.hom]
  [noetherian : IsNoetherian scheme.left]
  projective : IsProjectiveOverC scheme
attribute [instance] SmoothObject.variety SmoothObject.smooth SmoothObject.proper
  SmoothObject.noetherian

def product (X Y : SmoothObject) : PerverseSheaves.ComplexScheme :=
  Over.mk (pullback.fst X.scheme.hom Y.scheme.hom ≫ X.scheme.hom)
def firstProjection (X Y : SmoothObject) : product X Y ⟶ X.scheme :=
  Over.homMk (pullback.fst X.scheme.hom Y.scheme.hom) rfl
def secondProjection (X Y : SmoothObject) : product X Y ⟶ Y.scheme :=
  Over.homMk (pullback.snd X.scheme.hom Y.scheme.hom) pullback.condition.symm

class ProductGeometry (X Y : SmoothObject) : Prop where
  [variety : IsComplexVariety (product X Y)]
  [smooth : SmoothOfRelativeDimension (X.dimension + Y.dimension) (product X Y).hom]
  [proper : IsProper (product X Y).hom]
  projective : IsProjectiveOverC (product X Y)
attribute [instance] ProductGeometry.variety ProductGeometry.smooth ProductGeometry.proper

instance firstProjectionProper (X Y : SmoothObject) : IsProper (firstProjection X Y).left :=
  inferInstanceAs (IsProper (pullback.fst X.scheme.hom Y.scheme.hom))
instance secondProjectionProper (X Y : SmoothObject) : IsProper (secondProjection X Y).left :=
  inferInstanceAs (IsProper (pullback.snd X.scheme.hom Y.scheme.hom))

def diagonal (X : SmoothObject) : X.scheme ⟶ product X X :=
  Over.homMk (pullback.diagonal X.scheme.hom) (by simp [product])
instance diagonalClosed (X : SmoothObject) : IsClosedImmersion (diagonal X).left :=
  inferInstanceAs (IsClosedImmersion (pullback.diagonal X.scheme.hom))

abbrev Correspondence (X Y : SmoothObject) := ChowGroup (product X Y) Y.dimension

def diagonalClass (X : SmoothObject) : Correspondence X X :=
  (rationalEquivalences (product X X) X.dimension).mkQ
    (BettiCycleRealization.pushedFundamentalCycle (diagonal X) X.dimension)

variable
  (D : ∀ (X : PerverseSheaves.ComplexScheme) [IsComplexVariety X], DualizingComplex (space X))
  (P : ∀ {X Y : PerverseSheaves.ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
    (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f))
  (S : BettiCycleRealization.CycleRealization D P)
  [geometry : ∀ (X Y : SmoothObject), ProductGeometry X Y]

def action (X Y : SmoothObject) (n : ℤ) (a : Correspondence X Y) :
    BettiRealization.Cohomology (space X.scheme) n →ₗ[ℚ]
      BettiRealization.Cohomology (space Y.scheme) n :=
  BettiCycleRealization.cohomologyCast (by omega) ∘ₗ
    cohomologyPushforward (P (secondProjection X Y)) (D (product X Y)) (D Y.scheme)
      (X.dimension + Y.dimension) Y.dimension
      (S.toCycleMap.purity _ (X.dimension + Y.dimension)
        (ProductGeometry.projective (X := X) (Y := Y)))
      (S.toCycleMap.purity _ Y.dimension Y.projective) (2 * (X.dimension : ℤ) + n) ∘ₗ
    cupRight (space (product X Y))
      (BettiCycleRealization.cohomologyCast (by omega)
        (S.toCycleMap.cohomologyClass (product X Y) (X.dimension + Y.dimension) Y.dimension
          (ProductGeometry.projective (X := X) (Y := Y)) a)) ∘ₗ
    cohomologyPullback (spaceMap (firstProjection X Y)) n

def fiberProduct {Y U V : PerverseSheaves.ComplexScheme} (a : U ⟶ Y) (b : V ⟶ Y) :
    PerverseSheaves.ComplexScheme :=
  Over.mk (pullback.fst a.left b.left ≫ U.hom)
def fiberFirst {Y U V : PerverseSheaves.ComplexScheme} (a : U ⟶ Y) (b : V ⟶ Y) :
    fiberProduct a b ⟶ U := Over.homMk (pullback.fst a.left b.left) rfl
def fiberSecond {Y U V : PerverseSheaves.ComplexScheme} (a : U ⟶ Y) (b : V ⟶ Y) :
    fiberProduct a b ⟶ V := Over.homMk (pullback.snd a.left b.left) (by
      change pullback.snd a.left b.left ≫ V.hom = pullback.fst a.left b.left ≫ U.hom
      rw [← b.w, ← a.w, ← Category.assoc, ← pullback.condition, Category.assoc])

def pairMap {T : PerverseSheaves.ComplexScheme} (X Y : SmoothObject)
    (f : T ⟶ X.scheme) (g : T ⟶ Y.scheme) : T ⟶ product X Y :=
  Over.homMk (pullback.lift f.left g.left (by rw [f.w, g.w])) (by simp [product, f.w])

def compositionScheme {X Y Z U V : SmoothObject}
    (a : U.scheme ⟶ product X Y) (b : V.scheme ⟶ product Y Z) : PerverseSheaves.ComplexScheme :=
  fiberProduct (a ≫ secondProjection X Y) (b ≫ firstProjection Y Z)
def compositionMap {X Y Z U V : SmoothObject}
    (a : U.scheme ⟶ product X Y) (b : V.scheme ⟶ product Y Z) :
    compositionScheme a b ⟶ product X Z :=
  pairMap X Z
    (fiberFirst (a ≫ secondProjection X Y) (b ≫ firstProjection Y Z) ≫ a ≫ firstProjection X Y)
    (fiberSecond (a ≫ secondProjection X Y) (b ≫ firstProjection Y Z) ≫ b ≫ secondProjection Y Z)

class CorrespondenceCalculus where
  comp : ∀ X Y Z : SmoothObject,
    Correspondence X Y →ₗ[ℚ] Correspondence Y Z →ₗ[ℚ] Correspondence X Z
  id_comp : ∀ (X Y : SmoothObject) (a : Correspondence X Y), comp X X Y (diagonalClass X) a = a
  comp_id : ∀ (X Y : SmoothObject) (a : Correspondence X Y), comp X Y Y a (diagonalClass Y) = a
  assoc : ∀ (X Y Z W : SmoothObject) (a : Correspondence X Y) (b : Correspondence Y Z)
    (c : Correspondence Z W), comp X Z W (comp X Y Z a b) c = comp X Y W a (comp Y Z W b c)
  transverse_normalization : ∀ (X Y Z U V : SmoothObject)
    (a : U.scheme ⟶ product X Y) (b : V.scheme ⟶ product Y Z)
    [IsProper a.left] [IsProper b.left]
    (_dimU : U.dimension = Y.dimension) (_dimV : V.dimension = Z.dimension)
    [IsComplexVariety (compositionScheme a b)] [IsNoetherian (compositionScheme a b).left]
    [SmoothOfRelativeDimension Z.dimension (compositionScheme a b).hom]
    [IsProper (compositionMap a b).left],
    comp X Y Z
      ((rationalEquivalences (product X Y) Y.dimension).mkQ
        (BettiCycleRealization.pushedFundamentalCycle a Y.dimension))
      ((rationalEquivalences (product Y Z) Z.dimension).mkQ
        (BettiCycleRealization.pushedFundamentalCycle b Z.dimension)) =
      (rationalEquivalences (product X Z) Z.dimension).mkQ
        (BettiCycleRealization.pushedFundamentalCycle (compositionMap a b) Z.dimension)
  action_id : ∀ (X : SmoothObject) (n : ℤ), action D P S X X n (diagonalClass X) = LinearMap.id
  action_comp : ∀ (X Y Z : SmoothObject) (n : ℤ) (a : Correspondence X Y) (b : Correspondence Y Z),
    action D P S X Z n (comp X Y Z a b) = action D P S Y Z n b ∘ₗ action D P S X Y n a

structure CorrespondenceObject
    (D : ∀ (X : PerverseSheaves.ComplexScheme) [IsComplexVariety X], DualizingComplex (space X))
    (P : ∀ {X Y : PerverseSheaves.ComplexScheme} [IsComplexVariety X] [IsComplexVariety Y]
      (f : X ⟶ Y) [IsProper f.left], ProperPullback (spaceMap f))
    (_S : BettiCycleRealization.CycleRealization D P) where
  data : SmoothObject

variable [C : CorrespondenceCalculus D P S]

instance correspondenceCategory : Category.{0} (CorrespondenceObject D P S) where
  Hom X Y := Correspondence X.data Y.data
  id X := diagonalClass X.data
  comp a b := C.comp _ _ _ a b
  id_comp a := C.id_comp _ _ a
  comp_id a := C.comp_id _ _ a
  assoc a b c := C.assoc _ _ _ _ a b c

instance correspondencePreadditive : Preadditive (CorrespondenceObject D P S) where
  homGroup X Y := inferInstanceAs (AddCommGroup (Correspondence X.data Y.data))
  add_comp := by
    intro X Y Z a a' b
    exact congrArg (fun f => f b) ((C.comp X.data Y.data Z.data).map_add a a')
  comp_add := by intro X Y Z a b b'; exact (C.comp X.data Y.data Z.data a).map_add b b'

instance correspondenceLinear : Linear ℚ (CorrespondenceObject D P S) where
  homModule X Y := inferInstanceAs (Module ℚ (Correspondence X.data Y.data))
  smul_comp := by
    intro X Y Z r a b
    exact congrArg (fun f => f b) ((C.comp X.data Y.data Z.data).map_smul r a)
  comp_smul := by intro X Y Z a r b; exact (C.comp X.data Y.data Z.data a).map_smul r b

abbrev EffectiveChowMotive := Karoubi (CorrespondenceObject D P S)

def bettiFunctor (n : ℤ) : CorrespondenceObject D P S ⥤ ModuleCat.{1} ℚ where
  obj X := ModuleCat.of ℚ (BettiRealization.Cohomology (space X.data.scheme) n)
  map {X Y} a := ModuleCat.ofHom (action D P S X.data Y.data n a)
  map_id X := by ext a; exact congrArg (fun f => f a) (C.action_id X.data n)
  map_comp {X Y Z} a b := by
    ext x
    exact congrArg (fun f => f x) (C.action_comp X.data Y.data Z.data n a b)

theorem projector_idempotent (M : EffectiveChowMotive D P S) (n : ℤ) :
    action D P S M.X.data M.X.data n M.p ∘ₗ action D P S M.X.data M.X.data n M.p =
      action D P S M.X.data M.X.data n M.p := by
  rw [← C.action_comp]
  exact congrArg (action D P S M.X.data M.X.data n) M.idem

abbrev ProjectorSpace (M : EffectiveChowMotive D P S) (n : ℤ) :=
  LinearMap.range (action D P S M.X.data M.X.data n M.p)

def projectorMap {M N : EffectiveChowMotive D P S} (n : ℤ) (f : M ⟶ N) :
    ProjectorSpace D P S M n →ₗ[ℚ] ProjectorSpace D P S N n where
  toFun a := ⟨action D P S M.X.data N.X.data n f.f a.1, by
    have h : action D P S N.X.data N.X.data n N.p ∘ₗ action D P S M.X.data N.X.data n f.f =
        action D P S M.X.data N.X.data n f.f :=
      (C.action_comp M.X.data N.X.data N.X.data n f.f N.p).symm.trans
        (congrArg (action D P S M.X.data N.X.data n) (Karoubi.comp_p f))
    exact ⟨action D P S M.X.data N.X.data n f.f a.1, congrArg (fun g => g a.1) h⟩⟩
  map_add' a b := by ext; exact (action D P S M.X.data N.X.data n f.f).map_add a.1 b.1
  map_smul' r a := by ext; exact (action D P S M.X.data N.X.data n f.f).map_smul r a.1

def motiveBettiFunctor (n : ℤ) : EffectiveChowMotive D P S ⥤ ModuleCat.{1} ℚ where
  obj M := ModuleCat.of ℚ (ProjectorSpace D P S M n)
  map f := ModuleCat.ofHom (projectorMap D P S n f)
  map_id M := by
    ext a
    obtain ⟨x, hx⟩ := a.2
    change action D P S M.X.data M.X.data n M.p a.1 = a.1
    rw [← hx]
    exact congrArg (fun g => g x) (projector_idempotent D P S M n)
  map_comp {M N O} f g := by
    ext a
    exact congrArg (fun h => h a.1) (C.action_comp M.X.data N.X.data O.X.data n f.f g.f)

open scoped TensorProduct

def crossProduct (X Y : SmoothObject) (i j : ℤ) :
    BettiRealization.Cohomology (space X.scheme) i ⊗[ℚ]
      BettiRealization.Cohomology (space Y.scheme) j →ₗ[ℚ]
        BettiRealization.Cohomology (space (product X Y)) (i + j) :=
  TensorProduct.lift {
    toFun a := cupRight (space (product X Y))
      (cohomologyPullback (spaceMap (firstProjection X Y)) i a) ∘ₗ
      cohomologyPullback (spaceMap (secondProjection X Y)) j
    map_add' a b := by
      ext c
      change cup _ (cohomologyPullback (spaceMap (firstProjection X Y)) i (a + b)) _ = _
      rw [map_add]
      exact (cupLeft _ (cohomologyPullback (spaceMap (secondProjection X Y)) j c)).map_add _ _
    map_smul' r a := by
      ext c
      change cup _ (cohomologyPullback (spaceMap (firstProjection X Y)) i (r • a)) _ = _
      rw [map_smul]
      exact (cupLeft _ (cohomologyPullback (spaceMap (secondProjection X Y)) j c)).map_smul r _ }

abbrev KunnethDomain (X Y : SmoothObject) (n : ℤ) :=
  (i : Fin (2 * X.dimension + 1)) →
    BettiRealization.Cohomology (space X.scheme) (i : ℕ) ⊗[ℚ]
      BettiRealization.Cohomology (space Y.scheme) (n - (i : ℕ))

def kunnethComponent (X Y : SmoothObject) (n : ℤ) (i : Fin (2 * X.dimension + 1)) :
    KunnethDomain X Y n →ₗ[ℚ] BettiRealization.Cohomology (space (product X Y)) n :=
  BettiCycleRealization.cohomologyCast (by omega) ∘ₗ
    crossProduct X Y i (n - (i : ℕ)) ∘ₗ LinearMap.proj i

def kunnethMap (X Y : SmoothObject) (n : ℤ) :
    KunnethDomain X Y n →ₗ[ℚ] BettiRealization.Cohomology (space (product X Y)) n :=
  ∑ i : Fin (2 * X.dimension + 1), kunnethComponent X Y n i

omit C in theorem action_smul (X Y : SmoothObject) (n : ℤ) (a : Correspondence X Y) (r : ℚ) :
    action D P S X Y n (r • a) = r • action D P S X Y n a := by
  ext x
  simp only [action, LinearMap.comp_apply, LinearMap.smul_apply]
  simp [BettiRealization.cupRight, BettiRealization.cup, map_smul, Linear.smul_comp]

instance bettiFunctorLinear (n : ℤ) : (bettiFunctor D P S n).Linear ℚ where
  map_smul {X Y} a r := by
    apply ModuleCat.hom_ext
    change action D P S X.data Y.data n (r • a) = r • action D P S X.data Y.data n a
    exact action_smul D P S X.data Y.data n a r


instance motiveBettiFunctorLinear (n : ℤ) : (motiveBettiFunctor D P S n).Linear ℚ where
  map_smul {M N} f r := by
    ext a
    apply Subtype.ext
    change action D P S M.X.data N.X.data n (r • f.f) a.1 =
      r • action D P S M.X.data N.X.data n f.f a.1
    exact congrArg (fun g => g a.1) (action_smul D P S M.X.data N.X.data n f.f r)

end MathlibExt.AlgebraicGeometry.BettiMotiveRealization
