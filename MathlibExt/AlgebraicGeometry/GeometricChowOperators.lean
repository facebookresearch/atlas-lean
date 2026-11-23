/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.AlgebraicGeometry.GeometricChow
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Module.LinearMap.Rat
/-!
# Actual cycle pullback sums, residue-weighted push and integer Chow degrees

Cycle pullback is the literal sum of length-weighted fundamental cycles of
the inverse images of the reduced point closures. Pushforward is the literal
residue-degree-weighted sum. Both use the actual locally finite cycles,
which have finite support on the supplied Noetherian schemes.

The quotient maps use only proof inputs that those computed maps preserve
the actual geometric-family rational relations. The pullback equivalence
adds bijectivity of that fixed map; it does not supply an arbitrary operator.
These standing generic properties are source-proved in AxiomMath/Stacks
at c496df0d9beea9deaeabcea8492605f9a0a2313b, Chow/FlatPullback and
Chow/AffineBundle/VectorBundleFlatPullback.lean (02TY), and are not Wanted
claims here. Comparisons for the concrete geometric-family quotient require
explicit proof input rather than silently identifying presentations.

Integer degrees below zero are the actual zero module. This matters for
negative virtual dimension. The virtual zero-section map uses the inverse
of the computed bundle pullback, not a chosen virtual-class oracle.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.GeometricChowOperators
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeometricChow

variable (X : Scheme.{0}) [IsNoetherian X]

def pointClosure (x : X) : Scheme := (X.fromSpecResidueField x).ker.subscheme

def pointInclusion (x : X) : pointClosure X x ⟶ X :=
  (X.fromSpecResidueField x).ker.subschemeι

instance pointClosed (x : X) : IsClosedImmersion (pointInclusion X x) := by
  change IsClosedImmersion (X.fromSpecResidueField x).ker.subschemeι
  infer_instance
instance pointNoetherian (x : X) : IsNoetherian (pointClosure X x) := by
  let f := pointInclusion X x
  have : IsLocallyNoetherian (pointClosure X x) := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace (pointClosure X x) := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

def cycleFinsupp : AlgebraicCycle X ℚ →ₗ[ℚ] (X →₀ ℚ) where
  toFun c := Finsupp.ofSupportFinite c c.finite_support
  map_add' a b := by ext x; rfl
  map_smul' r a := by ext x; rfl

variable {X} {Y : Scheme.{0}} [IsNoetherian Y] (p : Y ⟶ X)

abbrev pointFiber (x : X) := pullback p (pointInclusion X x)

def fiberInclusion (x : X) : pointFiber p x ⟶ Y := pullback.fst p (pointInclusion X x)

instance fiberClosed (x : X) : IsClosedImmersion (fiberInclusion p x) := by
  change IsClosedImmersion (pullback.fst p (pointInclusion X x))
  infer_instance
instance fiberNoetherian (x : X) : IsNoetherian (pointFiber p x) := by
  let f := fiberInclusion p x
  have : IsLocallyNoetherian (pointFiber p x) := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace (pointFiber p x) := QuasiCompact.compactSpace_of_compactSpace f
  exact ⟨⟩

def basisPullback (d r : ℕ) (x : X) : CycleGroup Y (d + r) :=
  dimensionPart Y (d + r)
    (AlgebraicCycle.map (fiberInclusion p x) Order.height Order.height
      (fundamentalCycle (pointFiber p x)))

/-- The raw fibre-cycle transform: each point is sent to the dimension-`d + r` part of the
fundamental cycle of its fibre. It is the flat pullback only for a flat map of pure relative
dimension `r`; `FlatCycleDescent` records those hypotheses. -/
def flatCyclePullback (d r : ℕ) : CycleGroup X d →ₗ[ℚ] CycleGroup Y (d + r) :=
  Finsupp.linearCombination ℚ (basisPullback p d r) ∘ₗ cycleFinsupp X ∘ₗ
    (cyclesOfDimension X d).subtype

variable (X Y : ComplexScheme) [IsNoetherian X.left] [IsNoetherian Y.left]
  (f : Y ⟶ X) (r : ℕ)

/-- Flat pullback of relative dimension `r`: `f` is flat, every irreducible component of every
actual (scheme-theoretic) fibre `f.left.fiber x` has dimension `r`, and the fibre-cycle transform
preserves rational equivalence. -/
structure FlatCycleDescent : Prop where
  flat : Flat f.left
  pureDimension : ∀ (x : X.left) (Z : Set (f.left.fiber x)),
    Z ∈ irreducibleComponents (f.left.fiber x) → topologicalKrullDim Z = r
  preserves : ∀ d : ℕ, rationalEquivalences X d ≤
    (rationalEquivalences Y (d + r)).comap (flatCyclePullback f.left d r)

def chowPullbackNat (D : FlatCycleDescent X Y f r) (d : ℕ) :
    ChowGroup X d →ₗ[ℚ] ChowGroup Y (d + r) :=
  Submodule.mapQ _ _ (flatCyclePullback f.left d r) (D.preserves d)

def gradedChow (X : ComplexScheme) (d : ℤ) : ModuleCat.{0} ℚ :=
  if 0 ≤ d then ModuleCat.of ℚ (ChowGroup X d.toNat) else ModuleCat.of ℚ (Fin 0 → ℚ)

def positiveChowIso (X : ComplexScheme) (d : ℤ) (hd : 0 ≤ d) :
    gradedChow X d ≅ ModuleCat.of ℚ (ChowGroup X d.toNat) := by
  unfold gradedChow
  rw [ite_eq_left hd]

def chowCast (X : ComplexScheme) {d e : ℕ} (h : d = e) :
    ChowGroup X d →ₗ[ℚ] ChowGroup X e := by cases h; exact LinearMap.id

def gradedPullback (D : FlatCycleDescent X Y f r) (d : ℤ) :
    gradedChow X d →ₗ[ℚ] gradedChow Y (d + r) := by
  by_cases hd : 0 ≤ d
  · have ht : 0 ≤ d + r := by omega
    exact (positiveChowIso Y (d + r) ht).toLinearEquiv.symm.toLinearMap ∘ₗ
      chowCast Y (by omega) ∘ₗ chowPullbackNat X Y f r D d.toNat ∘ₗ
        (positiveChowIso X d hd).toLinearEquiv.toLinearMap
  · exact 0

structure ChowPullbackEquivalence where
  descent : FlatCycleDescent X Y f r
  bijective : ∀ d : ℤ, Function.Bijective (gradedPullback X Y f r descent d)

def pullbackEquiv (D : ChowPullbackEquivalence X Y f r) (d : ℤ) :
    gradedChow X d ≃ₗ[ℚ] gradedChow Y (d + r) :=
  LinearEquiv.ofBijective (gradedPullback X Y f r D.descent d) (D.bijective d)

def dimensionProjection (X : Scheme) (d : ℕ) : AlgebraicCycle X ℚ →ₗ[ℚ] CycleGroup X d where
  toFun := dimensionPart X d
  map_add' x y := by
    apply Subtype.ext
    ext p
    by_cases h : Order.height p = d
    · simp [dimensionPart, h]
    · simp [dimensionPart, h]
  map_smul' q x := by
    apply Subtype.ext
    ext p
    change (if Order.height p = d then q * x p else 0) =
      q * (if Order.height p = d then x p else 0)
    split_ifs <;> simp

variable {Z : ComplexScheme} [IsNoetherian Z.left] (i : Z ⟶ Y) [IsClosedImmersion i.left]

def closedPushBasis (d : ℕ) (x : Z.left) : CycleGroup Y.left d := by
  classical
  exact dimensionPart Y.left d
    (Function.locallyFinsuppWithin.single (i.left x) (i.left.residueDegree x : ℚ))

def closedCyclePush (d : ℕ) : CycleGroup Z.left d →ₗ[ℚ] CycleGroup Y.left d :=
  Finsupp.linearCombination ℚ (closedPushBasis Y i d) ∘ₗ cycleFinsupp Z.left ∘ₗ
    (cyclesOfDimension Z.left d).subtype

structure ClosedCycleDescent : Prop where
  preserves : ∀ d : ℕ, rationalEquivalences Z d ≤
    (rationalEquivalences Y d).comap (closedCyclePush Y i d)

def closedChowPush (D : ClosedCycleDescent Y i) (d : ℕ) : ChowGroup Z d →ₗ[ℚ] ChowGroup Y d :=
  Submodule.mapQ _ _ (closedCyclePush Y i d) (D.preserves d)

def gradedChowCast (X : ComplexScheme) {d e : ℤ} (h : d = e) :
    gradedChow X d →ₗ[ℚ] gradedChow X e := by cases h; exact LinearMap.id

def gradedClosedPush (D : ClosedCycleDescent Y i) (d : ℤ) :
    gradedChow Z d →ₗ[ℚ] gradedChow Y d := by
  by_cases hd : 0 ≤ d
  · exact (positiveChowIso Y d hd).toLinearEquiv.symm.toLinearMap ∘ₗ
      closedChowPush Y i D d.toNat ∘ₗ (positiveChowIso Z d hd).toLinearEquiv.toLinearMap
  · exact 0

end MathlibExt.AlgebraicGeometry.GeometricChowOperators
