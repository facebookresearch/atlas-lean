/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NumericalCurveCones
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Actual divisor degrees and first dynamical-degree growth

Numerical divisor classes are real degree functions on actual curve maps,
spanned by actual line bundles. Pullback is tested by composing each curve
map with the actual endomorphism. Intersection degrees are the multivariate
finite difference of the actual coherent Euler characteristic.

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

def lineDegrees {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (L : LineBundle X.left) : Curve X → ℝ := fun C ↦ curveDegrees C L

def NDiv {k : Type u} [Field k] (X : Over (Spec (.of k))) :
    Submodule ℝ (Curve X → ℝ) := Submodule.span ℝ (Set.range (lineDegrees (X := X)))

def composeCurve {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (f : X ⟶ X) (C : Curve X) : Curve X :=
  { C with map := C.map ≫ f }

def IsNefClass {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (v : NDiv X) : Prop := ∀ C : Curve X, 0 ≤ v.val C

def eulerCharacteristic {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (d : ℕ) (M : X.left.Modules) : ℤ :=
  ∑ i : Fin (d + 1), (-1 : ℤ) ^ i.val * Module.finrank k (cohomology X.hom M i.val)

def selectedTensor {X : Scheme.{u}} {d : ℕ} (L : Fin d → X.Modules)
    (S : Finset (Fin d)) : X.Modules :=
  S.toList.foldr (fun i M ↦ moduleTensor X (L i) M) (structureModule X)

/-- The d-fold first difference, with the native coherent Euler characteristic. -/
def mixedIntersection {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (d : ℕ) (L : Fin d → X.left.Modules) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
    (-1 : ℤ) ^ (d - S.card) * eulerCharacteristic X d (selectedTensor L S)

def iterateMap {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (f : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => iterateMap f n ≫ f

def firstDegree {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (d : ℕ) (H : LineBundle X.left) (f : X ⟶ X) : ℤ :=
  mixedIntersection X d (fun i : Fin d ↦
    if i.val = 0 then (Scheme.Modules.pullback f.left).obj H.val else H.val)

def degreeGrowth {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (d : ℕ) (H : LineBundle X.left) (f : X ⟶ X) (n : ℕ) : ℝ :=
  (max 0 (firstDegree d H (iterateMap f (n + 1)) : ℝ)) ^ (1 / (n + 1 : ℝ))

def firstDynamicalDegree {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (d : ℕ) (H : LineBundle X.left) (f : X ⟶ X) : ℝ :=
  Filter.limsup (degreeGrowth d H f) Filter.atTop

end MathlibExt.AlgebraicGeometry.DivisorDynamics
