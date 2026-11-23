/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NumericalCurveCones
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.KrullDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Actual divisor degrees and first dynamical-degree growth

Numerical divisor classes are real degree functions on actual curve maps,
spanned by actual line bundles. Pullback is tested by composing each curve
map with the actual endomorphism. Intersection degrees on a proper scheme of
dimension at most `d` are the `d`-fold multivariate finite difference of the
Euler characteristic of tensor products of line bundles (Snapper's polynomial;
Kleiman, *Toward a numerical theory of ampleness*, Chapter I §2): cohomology
vanishes above the dimension and is finite-dimensional for coherent sheaves, so
the alternating sum up to degree `d` is the Euler characteristic.

The growth sequence uses the first intersection degree of the actual
iterated pullback of an ample line. Its limsup defines the first dynamical
degree; convergence and a nef eigenclass are genuine theorem requests.

References: Fulton, *Intersection Theory*, Riemann–Roch and numerical
intersection theory; Truong, *Relative dynamical degrees of correspondences
over a field of arbitrary characteristic*, Theorem 1.1(1).
No dynamical-degree or pullback oracle is given.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DivisorDynamics

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurvePositivity
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open MathlibExt.AlgebraicGeometry.NumericalCurveCones
open scoped BigOperators

universe u

/-- The degree function of a line bundle on curves. -/
def lineDegrees {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (L : LineBundle X.left) : Curve X → ℝ := fun C ↦ curveDegrees C L

/-- Numerical divisor classes: the span of the degree functions of line bundles. -/
def NDiv {k : Type u} [Field k] (X : Over (Spec (.of k))) :
    Submodule ℝ (Curve X → ℝ) := Submodule.span ℝ (Set.range (lineDegrees (X := X)))

/-- The image of a curve under an endomorphism. -/
def composeCurve {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (f : X ⟶ X) (C : Curve X) : Curve X :=
  { C with map := C.map ≫ f }

/-- A numerical divisor class is nef when it is nonnegative on every curve. -/
def IsNefClass {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (v : NDiv X) : Prop := ∀ C : Curve X, 0 ≤ v.val C

/-- The Euler characteristic `∑_{i ≤ d} (-1)^i dim H^i(X, M)` of a module sheaf on a
proper scheme `X` over `k` of dimension at most `d`. Cohomology vanishes above the
dimension (Grothendieck vanishing) and is finite-dimensional for coherent `M`, such as
tensor products of line bundles (Serre), so this is `χ(X, M)` for those. -/
def eulerCharacteristic {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
    (d : ℕ) (_hd : topologicalKrullDim X.left ≤ d) (M : X.left.Modules) : ℤ :=
  ∑ i : Fin (d + 1), (-1 : ℤ) ^ i.val * Module.finrank k (cohomology X.hom M i.val)

/-- The tensor product of the sheaves `L i` for `i ∈ S`, the structure sheaf for `S = ∅`. -/
def selectedTensor {X : Scheme.{u}} {d : ℕ} (L : Fin d → X.Modules)
    (S : Finset (Fin d)) : X.Modules :=
  S.toList.foldr (fun i M ↦ moduleTensor X (L i) M) (structureModule X)

/-- The intersection number `(L₁ ⋯ L_d)` of `d` line bundles on a proper scheme of
dimension at most `d`: the `d`-fold mixed finite difference
`∑_{S ⊆ {1, …, d}} (-1)^{d - |S|} χ(⊗_{i ∈ S} L_i)` of the Euler characteristic. -/
def mixedIntersection {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
    (d : ℕ) (hd : topologicalKrullDim X.left ≤ d) (L : Fin d → X.left.Modules) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
    (-1 : ℤ) ^ (d - S.card) * eulerCharacteristic X d hd (selectedTensor L S)

/-- The `n`-th iterate `f^n` of an endomorphism. -/
def iterateMap {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (f : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => iterateMap f n ≫ f

/-- The first degree `(f^* H · H^{d - 1})` of an endomorphism with respect to `H`. -/
def firstDegree {k : Type u} [Field k] {X : Over (Spec (.of k))} [IsProper X.hom]
    (d : ℕ) (hd : topologicalKrullDim X.left ≤ d) (H : LineBundle X.left) (f : X ⟶ X) : ℤ :=
  mixedIntersection X d hd (fun i : Fin d ↦
    if i.val = 0 then (Scheme.Modules.pullback f.left).obj H.val else H.val)

/-- The growth sequence `deg₁(f^{n+1})^{1/(n+1)}`, with negative degrees read as `0`. -/
def degreeGrowth {k : Type u} [Field k] {X : Over (Spec (.of k))} [IsProper X.hom]
    (d : ℕ) (hd : topologicalKrullDim X.left ≤ d) (H : LineBundle X.left) (f : X ⟶ X)
    (n : ℕ) : ℝ :=
  (max 0 (firstDegree d hd H (iterateMap f (n + 1)) : ℝ)) ^ (1 / (n + 1 : ℝ))

/-- The first dynamical degree: the limit superior of the degree growth. -/
def firstDynamicalDegree {k : Type u} [Field k] {X : Over (Spec (.of k))} [IsProper X.hom]
    (d : ℕ) (hd : topologicalKrullDim X.left ≤ d) (H : LineBundle X.left) (f : X ⟶ X) : ℝ :=
  Filter.limsup (degreeGrowth d hd H f) Filter.atTop

end MathlibExt.AlgebraicGeometry.DivisorDynamics
