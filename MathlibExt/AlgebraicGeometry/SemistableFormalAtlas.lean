/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SemistableSkeletonRealization
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual étale semistable formal charts and proper pairs

The chart ring is the completion of the actual section algebra on a model
affine open. Its map from t0...tr=pi is the actual étale ring map, preserving
ground coefficients. Coordinates are computed through that map and completion.
Reduction uses the whole valuation maximal ideal. Horizontal divisors are
the actual closed subschemes whose affine ideals are the specified coordinates.
No discrete valuation or Noetherian valuation-ring hypothesis is imposed.

Reference: Gubler--Rabinoff--Werner, *Skeletons and tropicalizations*,
1404.7044v3, Definition 3.1 and sections 3--4. Ordinary étale/completion,
formal generic-fibre and proper model constructions are source dependencies.
Native completion and scheme operations: Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SemistableFormalAtlas

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry TopologicalSpace
open SemistableSkeletonRealization AffinoidFormalModels
open scoped BigOperators

variable (K : Type) [NormedField K] [IsUltrametricDist K]

abbrev ModelScheme := Over (Spec (CommRingCat.of (Integers K)))

abbrev StandardRing (n r : ℕ) (hr : r + 1 ≤ n) (pi : Integers K) :=
  standardQuotient K n r hr pi

instance standardCommRing (n r : ℕ) (hr : r + 1 ≤ n) (pi : Integers K) :
    CommRing (StandardRing K n r hr pi) := inferInstance

instance standardCommSemiring (n r : ℕ) (hr : r + 1 ≤ n) (pi : Integers K) :
    CommSemiring (StandardRing K n r hr pi) := (standardCommRing K n r hr pi).toCommSemiring

instance standardSemiring (n r : ℕ) (hr : r + 1 ≤ n) (pi : Integers K) :
    Semiring (StandardRing K n r hr pi) := (standardCommRing K n r hr pi).toSemiring

def scalarSections (X : ModelScheme K) (U : X.left.affineOpens) :
    Integers K →+* Γ(X.left, U.val) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (Integers K))).inv ≫
    X.hom.appLE ⊤ U.val (by intro x hx; trivial)).hom

structure StandardEtaleChart (X : ModelScheme K) where
  openSet : X.left.affineOpens
  n : ℕ
  r : ℕ
  s : ℕ
  bound : r + 1 + s ≤ n
  relationBound : r + 1 ≤ n
  pi : Integers K
  pi_nonzero : pi ≠ 0
  pi_small : ‖(pi : K)‖ < 1
  rawMap : StandardRing K n r relationBound pi →+* Γ(X.left, openSet.val)
  coefficients : ∀ a : Integers K,
    rawMap (algebraMap (Integers K) (StandardRing K n r relationBound pi) a) =
      scalarSections K X openSet a
  etale : letI := rawMap.toAlgebra
    Algebra.Etale (StandardRing K n r relationBound pi) Γ(X.left, openSet.val)
  model : AffinoidFormalModel (Integers K) K pi
  completion : AdicCompletion ((SemistableSkeletonRealization.parameterIdeal K pi).map
    (scalarSections K X openSet)) Γ(X.left, openSet.val) ≃+* model.modelRing
  completion_coefficients : ∀ a : Integers K,
    completion (AdicCompletion.of
      ((SemistableSkeletonRealization.parameterIdeal K pi).map (scalarSections K X openSet))
      Γ(X.left, openSet.val) (scalarSections K X openSet a)) =
        algebraMap (Integers K) model.modelRing a

variable {K} {X : ModelScheme K} (C : StandardEtaleChart K X)

def completedSection (a : Γ(X.left, C.openSet.val)) : C.model.modelRing :=
  C.completion (AdicCompletion.of
    ((SemistableSkeletonRealization.parameterIdeal K C.pi).map
      (scalarSections K X C.openSet)) Γ(X.left, C.openSet.val) a)

def rawCoordinate (j : Fin C.n) : Γ(X.left, C.openSet.val) :=
  C.rawMap (standardCoordinate K C.n C.r C.relationBound C.pi j)

def coordinate (j : Fin C.n) : C.model.modelRing := completedSection C (rawCoordinate C j)

def specialIdeal : Ideal C.model.modelRing :=
  (IsLocalRing.maximalIdeal (Integers K)).map (algebraMap (Integers K) C.model.modelRing)

abbrev SpecialRing := C.model.modelRing ⧸ specialIdeal C

structure Reduction where
  map : C.model.GenericPoint → PrimeSpectrum (SpecialRing C)
  normalized : ∀ (p : C.model.GenericPoint) (a : C.model.modelRing),
    Ideal.Quotient.mk (specialIdeal C) a ∈ (map p).asIdeal ↔
      p.val.seminorm (algebraMap C.model.modelRing C.model.genericAlgebra a) < 1

def coordinateNorm (p : C.model.GenericPoint) (j : Fin C.n) : ℝ :=
  p.val.seminorm (algebraMap C.model.modelRing C.model.genericAlgebra (coordinate C j))

def valuationCoordinate (p : C.model.GenericPoint) (j : Fin C.n) : ENNReal :=
  if coordinateNorm C p j = 0 then ⊤ else ENNReal.ofReal (-Real.log (coordinateNorm C p j))

def coordinateStratum (I : Finset (Fin C.n)) : Set (PrimeSpectrum (SpecialRing C)) :=
  {x | ∀ j : Fin C.n, j.val < C.r + 1 + C.s →
    (Ideal.Quotient.mk (specialIdeal C) (coordinate C j) ∈ x.asIdeal ↔ j ∈ I)}

/-- A stratum: an irreducible component of the locally closed locus where exactly the prescribed
coordinates vanish. Its generic point is taken in the locus, with the subspace topology; a
stratum need not be closed in the special fibre (the open stratum `T ≠ 0` of the affine line is
not), so it is not the closure of its generic point there. -/
structure Stratum where
  vanishing : Finset (Fin C.n)
  allowed : ∀ j ∈ vanishing, j.val < C.r + 1 + C.s
  locusComponent : Set (coordinateStratum C vanishing)
  maximal_irreducible : locusComponent ∈ irreducibleComponents (coordinateStratum C vanishing)
  component : Set (PrimeSpectrum (SpecialRing C))
  component_eq : component = Subtype.val '' locusComponent
  genericPoint : coordinateStratum C vanishing
  generic : IsGenericPoint genericPoint locusComponent

def coordinateFibre (R : Reduction C) (S : Stratum C) (p : C.model.GenericPoint) :
    Set C.model.GenericPoint :=
  {q | R.map q ∈ S.component ∧ ∀ j : Fin (C.r + 1 + C.s),
    coordinateNorm C q ⟨j.val, j.isLt.trans_le C.bound⟩ =
      coordinateNorm C p ⟨j.val, j.isLt.trans_le C.bound⟩}

/-- The entire point is fixed by its actual singleton Shilov boundary. -/
def IsGaussPoint (R : Reduction C) (S : Stratum C) (p q : C.model.GenericPoint) : Prop :=
  q ∈ coordinateFibre C R S p ∧ R.map q = S.genericPoint.val ∧
    ∀ (a : C.model.genericAlgebra) (z : C.model.GenericPoint),
      z ∈ coordinateFibre C R S p → z.val.seminorm a ≤ q.val.seminorm a

def localSkeleton (R : Reduction C) : Set C.model.GenericPoint :=
  {p | ∃ S : Stratum C, IsGaussPoint C R S p p}

def parameterDomain : Set (Fin (C.r + 1 + C.s) → ENNReal) :=
  {v | (∑ j : Fin (C.r + 1), v ⟨j.val, by omega⟩) =
    ENNReal.ofReal (-Real.log ‖(C.pi : K)‖)}

def valuationParameters (p : C.model.GenericPoint) : Fin (C.r + 1 + C.s) → ENNReal :=
  fun j ↦ valuationCoordinate C p ⟨j.val, j.isLt.trans_le C.bound⟩

variable (K)

structure StrictPair where
  model : ModelScheme K
  [integralModel : IsIntegral model.left]
  [properModel : IsProper model.hom]
  [flatModel : Flat model.hom]
  [finitePresentation : LocallyOfFinitePresentation model.hom]
  generic : Over (Spec (CommRingCat.of K))
  genericIso : generic.left ≅ pullback model.hom
    (Spec.map (CommRingCat.ofHom (algebraMap (Integers K) K)))
  generic_projection : genericIso.hom ≫ pullback.snd model.hom
    (Spec.map (CommRingCat.ofHom (algebraMap (Integers K) K))) = generic.hom
  dimension : ℕ
  [properGeneric : IsProper generic.hom]
  [smoothGeneric : SmoothOfRelativeDimension dimension generic.hom]
  boundarySize : ℕ
  boundary : Fin boundarySize → ModelScheme K
  [integralBoundary : ∀ i, IsIntegral (boundary i).left]
  boundaryInclusion : ∀ i, (boundary i) ⟶ model
  [closedBoundary : ∀ i, IsClosedImmersion (boundaryInclusion i).left]
  [flatBoundary : ∀ i, Flat (boundary i).hom]
  atlasSize : ℕ
  chart : Fin atlasSize → StandardEtaleChart K model
  chart_dimension : ∀ i, (chart i).n = dimension + 1
  cover : ∀ x : model.left, ∃ i, x ∈ (chart i).openSet.val
  horizontal : ∀ i, Fin (chart i).s ↪ Fin boundarySize
  boundaryEquation : ∀ (i : Fin atlasSize) (j : Fin (chart i).s),
    RingHom.ker (((chart i).openSet.val.topIso.inv ≫
      (pullback.snd (boundaryInclusion (horizontal i j)).left
        (chart i).openSet.val.ι).appTop).hom) =
      Ideal.span {rawCoordinate (chart i) ⟨(chart i).r + 1 + j.val, by
        have hj := j.isLt
        have hb := (chart i).bound
        omega⟩}
  boundaryEmpty : ∀ (i : Fin atlasSize) (j : Fin boundarySize),
    j ∉ Set.range (horizontal i) →
    RingHom.ker (((chart i).openSet.val.topIso.inv ≫
      (pullback.snd (boundaryInclusion j).left (chart i).openSet.val.ι).appTop).hom) = ⊤

attribute [instance] StrictPair.integralModel StrictPair.integralBoundary
  StrictPair.properModel StrictPair.flatModel StrictPair.finitePresentation
  StrictPair.properGeneric StrictPair.smoothGeneric StrictPair.closedBoundary
  StrictPair.flatBoundary

variable {K} (P : StrictPair K)

def genericToModel : P.generic.left ⟶ P.model.left :=
  P.genericIso.hom ≫ pullback.fst P.model.hom
    (Spec.map (CommRingCat.ofHom (algebraMap (Integers K) K)))

def specialFibre : Scheme := pullback P.model.hom
  (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Integers K))))

def specialToModel : specialFibre P ⟶ P.model.left := pullback.fst P.model.hom
  (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Integers K))))

end MathlibExt.AlgebraicGeometry.SemistableFormalAtlas
