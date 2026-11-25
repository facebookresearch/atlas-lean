/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NumericalCurveCones
public import MathlibExt.AlgebraicGeometry.SmoothKrullDim
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Topology.KrullDimension
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Actual divisor degrees and first dynamical-degree growth

Numerical divisor classes are real degree functions on actual curve maps,
spanned by actual line bundles. Pullback is tested by composing each curve
map with the actual endomorphism.

The intersection number of `d` line bundles on a proper scheme of dimension at
most `d` is the `d`-fold mixed finite difference of the Euler characteristic of
their tensor products (Snapper's polynomial; Kleiman, *Toward a numerical theory
of ampleness*, Chapter I §2). Tensor products of line bundles are coherent, so
on a proper scheme their cohomology is finite-dimensional (Serre), and it
vanishes above the dimension (Grothendieck), so the alternating sum of the
cohomology dimensions up to degree `d`, `truncatedEuler`, is their Euler
characteristic. For an arbitrary module sheaf `truncatedEuler` is only that
alternating sum.

The growth sequence uses the first intersection degree `(f^* H · H^{d - 1})`
of the iterates of an endomorphism of a proper scheme of dimension `d > 0`. Its
limsup is the first dynamical degree of a dominant endomorphism of a proper
integral scheme with respect to an ample line bundle; convergence, independence
of the ample line bundle and a nef eigenclass are theorem requests.

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

/-- The alternating sum `∑_{i ≤ d} (-1)^i dim_k H^i(X, M)` of the cohomology dimensions
of a module sheaf in degrees at most `d`. It is the Euler characteristic `χ(X, M)` when
these cohomology spaces are finite-dimensional and cohomology vanishes above `d`, for
instance for a coherent sheaf on a proper scheme of dimension at most `d`. -/
def truncatedEuler {k : Type u} [Field k] (X : Over (Spec (.of k))) (d : ℕ)
    (M : X.left.Modules) : ℤ :=
  ∑ i : Fin (d + 1), (-1 : ℤ) ^ i.val * Module.finrank k (cohomology X.hom M i.val)

/-- The tensor product of the sheaves `L i` for `i ∈ S`, the structure sheaf for `S = ∅`. -/
def selectedTensor {X : Scheme.{u}} {d : ℕ} (L : Fin d → X.Modules)
    (S : Finset (Fin d)) : X.Modules :=
  S.toList.foldr (fun i M ↦ moduleTensor X (L i) M) (structureModule X)

/-- The intersection number `(L₁ ⋯ L_d)` of `d` line bundles on a proper scheme of
dimension at most `d`: the `d`-fold mixed finite difference
`∑_{S ⊆ {1, …, d}} (-1)^{d - |S|} χ(⊗_{i ∈ S} L_i)` of the Euler characteristic. -/
def mixedIntersection {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
    (d : ℕ) (_hd : topologicalKrullDim X.left ≤ d) (L : Fin d → LineBundle X.left) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
    (-1 : ℤ) ^ (d - S.card) * truncatedEuler X d (selectedTensor (fun i ↦ (L i).val) S)

/-- The pullback of a line bundle along a morphism of schemes. -/
def pullbackLine {X Y : Scheme.{u}} (f : X ⟶ Y) (L : LineBundle Y) : LineBundle X :=
  ⟨(Scheme.Modules.pullback f).obj L.val, L.2.pullback f⟩

/-- The `n`-th iterate `f^n` of an endomorphism. -/
def iterateMap {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (f : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => iterateMap f n ≫ f

/-- The first degree `(f^* H · H^{d - 1})` of an endomorphism of a proper scheme of
dimension `d > 0` with respect to a line bundle `H`. -/
def firstDegree {k : Type u} [Field k] {X : Over (Spec (.of k))} [IsProper X.hom]
    (d : ℕ) (hd : topologicalKrullDim X.left = d) (_hd₀ : 0 < d) (H : LineBundle X.left)
    (f : X ⟶ X) : ℤ :=
  mixedIntersection X d hd.le (fun i : Fin d ↦ if i.val = 0 then pullbackLine f.left H else H)

/-- The growth sequence `deg₁(f^{n+1})^{1/(n+1)}` of the first degrees of the iterates,
with negative degrees read as `0`. -/
def degreeGrowth {k : Type u} [Field k] {X : Over (Spec (.of k))} [IsProper X.hom]
    (d : ℕ) (hd : topologicalKrullDim X.left = d) (hd₀ : 0 < d) (H : LineBundle X.left)
    (f : X ⟶ X) (n : ℕ) : ℝ :=
  (max 0 (firstDegree d hd hd₀ H (iterateMap f (n + 1)) : ℝ)) ^ (1 / (n + 1 : ℝ))

/-- The first dynamical degree of a dominant endomorphism `f` of a proper integral scheme
of dimension `d > 0`, computed with an ample line bundle `H`: the limit superior of the
degree growth. -/
def firstDynamicalDegree {k : Type u} [Field k] {X : Over (Spec (.of k))} [IsIntegral X.left]
    [IsProper X.hom] [IsNoetherian X.left] (d : ℕ) (hd : topologicalKrullDim X.left = d)
    (hd₀ : 0 < d) (H : LineBundle X.left) (_hH : IsAmpleLine H) (f : X ⟶ X)
    [IsDominant f.left] : ℝ :=
  Filter.limsup (degreeGrowth d hd hd₀ H f) Filter.atTop

/-- A nonempty scheme smooth of relative dimension `d` over a field has dimension `d`. -/
theorem topologicalKrullDim_eq_of_smooth {k : Type u} [Field k] (X : Over (Spec (.of k)))
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] [Nonempty X.left] :
    topologicalKrullDim X.left = d :=
  le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le X.hom d)
    (SmoothOfRelativeDimension.le_topologicalKrullDim X.hom d)

end MathlibExt.AlgebraicGeometry.DivisorDynamics
