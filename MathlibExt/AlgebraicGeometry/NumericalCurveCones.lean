/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LineBundlePullback
public import MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Topology.Constructions
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Numerical curves and the Mori cone

Curve classes are actual degree functions on actual line bundles. The
numerical space is their real linear span; its topology is the inherited
pointwise topology on degree functions. The Mori cone is the closure of
finite nonnegative combinations of those genuine curve classes.

No arbitrary intersection pairing, numerical lattice or cone is supplied.
Finite dimensionality identifies this intrinsic weak topology with the
usual finite-dimensional numerical topology in the requested theorem.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NumericalCurveCones

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open scoped BigOperators

universe u

/-- A curve on `X`: a morphism to `X` from a proper integral curve over `k`, possibly
singular. Every proper integral curve in `X` is one, with its inclusion, so this works over
every field, including imperfect fields, where an integral curve need not be the image of a
smooth curve. -/
structure Curve {k : Type u} [Field k] (X : Over (Spec (.of k))) where
  /-- The source curve. -/
  source : Over (Spec (.of k))
  [properCurve : IsProperCurve source.hom]
  [integral : IsIntegral source.left]
  /-- The morphism to `X`. -/
  map : source ⟶ X

attribute [instance] Curve.properCurve Curve.integral

/-- The degree of every line bundle on `X` along a curve: the degree of its pullback to
the source curve. -/
def curveDegrees {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : Curve X) : LineBundle X.left → ℝ :=
  fun L ↦ (degree C.source.hom ((Scheme.Modules.pullback C.map.left).obj L.val)
    (L.2.pullback C.map.left) : ℝ)

def N1 {k : Type u} [Field k] (X : Over (Spec (.of k))) :
    Submodule ℝ (LineBundle X.left → ℝ) :=
  Submodule.span ℝ (Set.range (curveDegrees (X := X)))

instance {k : Type u} [Field k] (X : Over (Spec (.of k))) :
    TopologicalSpace (N1 X) :=
  TopologicalSpace.induced
    ((↑) : N1 X → LineBundle X.left → ℝ) inferInstance

def curveClass {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : Curve X) : N1 X :=
  ⟨curveDegrees C, Submodule.subset_span (Set.mem_range_self C)⟩

def effectiveCombinations {k : Type u} [Field k]
    (X : Over (Spec (.of k))) : Set (N1 X) :=
  {v | ∃ m : ℕ, ∃ C : Fin m → Curve X, ∃ a : Fin m → ℝ,
    (∀ i, 0 ≤ a i) ∧ v = ∑ i, a i • curveClass (C i)}

def moriCone {k : Type u} [Field k] (X : Over (Spec (.of k))) : Set (N1 X) :=
  closure (effectiveCombinations X)

def ray {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (v : N1 X) : Set (N1 X) :=
  {w | ∃ a : ℝ, 0 ≤ a ∧ a • v = w}

def IsExtremalRay {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (v : N1 X) : Prop :=
  v ≠ 0 ∧ v ∈ moriCone X ∧
    ∀ x ∈ moriCone X, ∀ y ∈ moriCone X, x + y ∈ ray v →
      x ∈ ray v ∧ y ∈ ray v

def IsNefLine {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (L : LineBundle X.left) : Prop :=
  ∀ C : Curve X, 0 ≤ curveDegrees C L

def nefPencil {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (H K : LineBundle X.left) (t : ℝ) : Prop :=
  ∀ C : Curve X, 0 ≤ curveDegrees C H + t * curveDegrees C K

end MathlibExt.AlgebraicGeometry.NumericalCurveCones
