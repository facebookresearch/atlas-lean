/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RelativeProjectivity
public import MathlibExt.AlgebraicGeometry.LogPairs
public import MathlibExt.AlgebraicGeometry.MoriContractionModels
public import MathlibExt.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Relative numerical and log contraction contracts

Relative numerical classes are the actual span of curve-degree functions for
curves contracted by the chosen scheme map. Its cone is the closure of actual
nonnegative combinations. Log adjoint degrees use the actual Cartier-line
representative from `LogPairs`, with no smooth or absolute-proper assumption
on the source. Contractions and flips retain their actual maps over the base,
structure-sheaf unit, connected fibres and normalized codimension-one boundary.

These are minimal reusable contracts; existence and representative/model
comparison proofs are separate Wanted obligations. No general termination,
abundance or conjectural model provider is asserted.
References: Kollár--Mori, Chapter3; BCHM, Corollary1.4.1 (flips).
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeMoriContracts

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open MathlibExt.AlgebraicGeometry.CurvePositivity
open MathlibExt.AlgebraicGeometry.NumericalCurveCones
open MathlibExt.AlgebraicGeometry.MoriContractionModels
open MathlibExt.AlgebraicGeometry.RationalResolution
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.RelativeProjectivity
open scoped BigOperators

universe u

variable {k : Type u} [Field k]
variable {X S : Over (Spec (.of k))}

def IsQuasiProjectiveBase (S : Over (Spec (.of k))) : Prop :=
  ∃ m : ℕ, ∃ i : S ⟶ ProjectiveSpace.projectiveSpace k m, IsImmersion i.left

/-- Relative N1 is a subspace of the existing actual degree-function space. -/
def RelativeN1 (q : X ⟶ S) : Submodule ℝ (N1 X) :=
  Submodule.span ℝ {v | ∃ C : Curve X, IsContracted q C ∧ curveClass C = v}

def relativeClass (q : X ⟶ S) (C : Curve X) (h : IsContracted q C) : RelativeN1 q :=
  ⟨curveClass C, Submodule.subset_span ⟨C, h, rfl⟩⟩

def relativeEffective (q : X ⟶ S) : Set (RelativeN1 q) :=
  {v | ∃ m : ℕ, ∃ C : Fin m → Curve X, ∃ h : ∀ i, IsContracted q (C i),
    ∃ a : Fin m → ℝ, (∀ i, 0 ≤ a i) ∧ v = ∑ i, a i • relativeClass q (C i) (h i)}

def relativeCone (q : X ⟶ S) : Set (RelativeN1 q) := closure (relativeEffective q)

def relativeRay {q : X ⟶ S} (v : RelativeN1 q) : Set (RelativeN1 q) :=
  {w | ∃ a : ℝ, 0 ≤ a ∧ a • v = w}

def IsExtremal {q : X ⟶ S} (v : RelativeN1 q) : Prop :=
  v ≠ 0 ∧ v ∈ relativeCone q ∧ ∀ x ∈ relativeCone q, ∀ y ∈ relativeCone q,
    x + y ∈ relativeRay v → x ∈ relativeRay v ∧ y ∈ relativeRay v

variable {n : ℕ}

def combinationOnCurve {V : NormalVariety k n} (D : CartierCombination V) (C : Curve V.X) : ℝ :=
  ∑ i, D.coefficients i * curveDegrees C (D.components i).line

def combinationOnClass {V : NormalVariety k n} (q : V.X ⟶ S)
    (D : CartierCombination V) (v : RelativeN1 q) : ℝ :=
  ∑ i, D.coefficients i * v.val.val (D.components i).line

def negativeCombination {V : NormalVariety k n} (D : CartierCombination V) : CartierCombination V :=
  { D with coefficients := fun i => -D.coefficients i }

/-- R-ampleness uses a nonempty positive actual ample-Cartier representative. -/
def IsRelativelyAmpleR {V : NormalVariety k n} (q : V.X ⟶ S) (D : CartierCombination V) : Prop :=
  ∃ E : CartierCombination V, E.divisor = D.divisor ∧ 0 < E.size ∧
    ∀ i, 0 < E.coefficients i ∧ IsRelativelyAmple q (E.components i).line

/-- Relative generation is the actual pullback/direct-image evaluation map. -/
def IsRelativelyGenerated (q : X ⟶ S) (M : X.left.Modules) : Prop :=
  Epi ((Scheme.Modules.pullbackPushforwardAdjunction q.left).counit.app M)

def IsRelativelySemiample (q : X ⟶ S) (L : LineBundle X.left) : Prop :=
  ∃ m : ℕ, 0 < m ∧ IsRelativelyGenerated q (power L.val m)

structure RelativeContraction (P : LogPair k n) (q : P.variety.X ⟶ S) (v : RelativeN1 q) where
  target : Over (Spec (.of k))
  [integral : IsIntegral target.left]
  [noetherian : IsNoetherian target.left]
  normal : IsNormalIntegral target.left
  toBase : target ⟶ S
  projectiveBase : IsHProjectiveOver toBase
  map : P.variety.X ⟶ target
  [proper : IsProper map.left]
  projective : IsHProjectiveOver map
  [connected : GeometricallyConnected map.left]
  unit : IsIso (structureUnit map.left)
  over : map ≫ toBase = q
  curves : ∀ C : Curve P.variety.X, ∀ h : IsContracted q C,
    IsContracted map C ↔ relativeClass q C h ∈ relativeRay v

attribute [instance] RelativeContraction.integral RelativeContraction.noetherian
  RelativeContraction.proper RelativeContraction.connected

structure RelativeFlip {P : LogPair k n} {q : P.variety.X ⟶ S} {v : RelativeN1 q}
    (C : RelativeContraction P q v) where
  source : LogPair k n
  /-- The flipped pair is klt; this includes its model calculus. -/
  klt : IsKlt source
  qfactorial : IsQFactorial source.variety
  map : source.variety.X ⟶ C.target
  [proper : IsProper map.left]
  projective : IsHProjectiveOver map
  unit : IsIso (structureUnit map.left)
  small : IsSmall map.left n
  identification : Scheme.PartialIso P.variety.X.left source.variety.X.left
  sourceBig : ∀ p : PrimePoint P.variety, p.val ∈ identification.source
  targetBig : ∀ p : PrimePoint source.variety, p.val ∈ identification.target
  over : identification.iso.hom ≫ identification.target.ι ≫ map.left =
    identification.source.ι ≫ C.map.left
  primeEquiv : PrimePoint P.variety ≃ PrimePoint source.variety
  primeNormalized : ∀ p,
    (primeEquiv p).val = identification.target.ι
      (identification.iso.hom ⟨p.val, sourceBig p⟩)
  boundary : ∀ p, source.boundary (primeEquiv p) = P.boundary p
  adjointAmple : IsRelativelyAmpleR map source.adjoint

end MathlibExt.AlgebraicGeometry.RelativeMoriContracts
