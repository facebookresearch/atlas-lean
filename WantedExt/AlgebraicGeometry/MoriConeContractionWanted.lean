/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.PlurigenusFamilies
public import MathlibExt.AlgebraicGeometry.MoriContractionModels

/-!
# Numerical MMP foundations, Mori contractions and flips

The numerical space and cone are built from actual curve degrees. Canonical
lines, ample systems, contracted curves and small birational maps have fixed
geometric meanings. These requests are in the smooth projective
characteristic-zero scope; no general termination or abundance statement is
used as established background.

References: Kollár–Mori, *Birational Geometry of Algebraic Varieties*,
Chapter 3; Birkar–Cascini–Hacon–McKernan, *Existence of minimal models for
varieties of log general type*, for existence of flips.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MoriConeContractionWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry (ProjectiveSpace.IsProjective)
open MathlibExt.AlgebraicGeometry.ProjectiveLineSystems
open MathlibExt.AlgebraicGeometry.NumericalCurveCones
open MathlibExt.AlgebraicGeometry.MoriContractionModels
open MathlibExt.AlgebraicGeometry.PlurigenusFamilies
open MathlibExt.AlgebraicGeometry.CurvePositivity
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open scoped BigOperators

universe u

/-- The real space $N_1(X)$ of numerical curve classes is finite-dimensional, for $X$ an integral,
proper and projective $k$-scheme smooth of relative dimension $n$ over an algebraically closed field
$k$ of characteristic zero. Here $N_1(X)$ is the real span of the functions $L ↦ \deg(L|_C)$ on line
bundles, for the curves $C → X$. -/
theorem_wanted numerical_finiteDimensional (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (projective : ProjectiveSpace.IsProjective X)
    : FiniteDimensional ℝ (N1 X)

/-- The cone theorem: let $k$ be an algebraically closed field of characteristic zero, $X$ an
integral, proper, Noetherian and projective $k$-scheme smooth of relative dimension $n$, $K$ its
canonical line bundle (characterized by Serre duality, `hK`), $H$ an ample line bundle and $ε > 0$.
Then there are finitely many curves $C_1, …, C_m$ on $X$, each of genus zero with
$0 < -K·C_i ≤ n + 1$ and spanning an extremal ray of the Mori cone $\overline{NE}(X)$, such that
every $v ∈ \overline{NE}(X)$ is $w + \sum_i a_i [C_i]$ with all $a_i ≥ 0$ and $w ∈ \overline{NE}(X)$
satisfying $(K + εH)·w ≥ 0$. -/
theorem_wanted cone (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    [IsNoetherian X.left]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (projective : ProjectiveSpace.IsProjective X)
    (K H : LineBundle X.left)
    (hK : SerreDualizingLine X.hom K.val n) (hH : IsAmpleLine H)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, ∃ C : Fin m → Curve X,
      (∀ i, genus (C i).source.hom = 0 ∧
        0 < -curveDegrees (C i) K ∧ -curveDegrees (C i) K ≤ n + 1 ∧
        IsExtremalRay (curveClass (C i))) ∧
      ∀ v ∈ moriCone X, ∃ w ∈ moriCone X,
        0 ≤ w.val K + ε * w.val H ∧
        ∃ a : Fin m → ℝ, (∀ i, 0 ≤ a i) ∧
          v = w + ∑ i, a i • curveClass (C i)

/-- The rationality theorem: let $k$ be an algebraically closed field of characteristic zero, $X$ an
integral, proper, Noetherian and projective $k$-scheme smooth of relative dimension $n$, $K$ its
canonical line bundle (characterized by Serre duality, `hK`) and $H$ an ample line bundle, and
suppose that $K·C < 0$ for some curve $C$ on $X$. Then there is a rational number $r > 0$ with
denominator at most $n + 1$ such that for every real $t ≥ 0$, $H + tK$ is nef (nonnegative on every
curve) if and only if $t ≤ r$. -/
theorem_wanted rationality (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    [IsNoetherian X.left]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (projective : ProjectiveSpace.IsProjective X)
    (K H : LineBundle X.left)
    (hK : SerreDualizingLine X.hom K.val n) (hH : IsAmpleLine H)
    (negative : ∃ C : Curve X, curveDegrees C K < 0) :
    ∃ r : ℚ, 0 < r ∧ r.den ≤ n + 1 ∧
      ∀ t : ℝ, 0 ≤ t → (nefPencil H K t ↔ t ≤ (r : ℝ))

/-- The base-point-free theorem: let $k$ be an algebraically closed field of characteristic zero,
$X$ an integral, proper, Noetherian and projective $k$-scheme smooth of relative dimension $n$, $K$
its canonical line bundle (characterized by Serre duality, `hK`) with a chosen inverse $K^{-1}$, and
$L$ a nef line bundle such that, for some $a > 0$, $L^{⊗ a} ⊗ K^{-1}$ is a line bundle that is
ample. Then $L$ is semiample: some positive tensor power of $L$ is generated by global sections. -/
theorem_wanted basepointFree (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    [IsNoetherian X.left]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (projective : ProjectiveSpace.IsProjective X)
    (K L : LineBundle X.left)
    (hK : SerreDualizingLine X.hom K.val n) (Kinv : InverseLine K)
    (nef : IsNefLine L) (a : ℕ) (ha : 0 < a)
    (hLine : IsLineBundle
      (moduleTensor X.left (power L.val a) Kinv.inverse.val))
    (ample : IsAmpleLine
      ⟨moduleTensor X.left (power L.val a) Kinv.inverse.val, hLine⟩) :
    IsSemiample L.val L.property

/-- Contraction of a $K$-negative extremal ray: let $k$ be an algebraically closed field of
characteristic zero, $X$ an integral, proper, projective $k$-scheme smooth of relative dimension
$n$, $K$ its canonical line bundle (characterized by Serre duality, `hK`) and $v$ a class spanning
an extremal ray of the Mori cone with $K·v < 0$. Then there is a contraction of $v$
(`Contraction X v`): a proper, locally projective morphism $f : X → Y$ to a normal integral proper
projective $k$-scheme, with geometrically connected fibres, for which
$\mathcal O_Y → f_*\mathcal O_X$ is an isomorphism, and which contracts a curve exactly when its
class lies on the ray spanned by $v$. -/
def_wanted contraction (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (projective : ProjectiveSpace.IsProjective X)
    (K : LineBundle X.left)
    (hK : SerreDualizingLine X.hom K.val n)
    (v : N1 X) (ray : IsExtremalRay v) (negative : v.val K < 0) :
    Contraction X v

/-- Existence of flips: let $k$ be an algebraically closed field of characteristic zero, $X$ an
integral, proper, Noetherian and projective $k$-scheme smooth of relative dimension $n ≥ 3$, $K$ its
canonical line bundle (characterized by Serre duality, `hK`), $v$ a class spanning an extremal ray
of the Mori cone with $K·v < 0$, and `C` a contraction of $v$, with target $Y$, that is small and
over which a chosen inverse $K^{-1}$ is relatively ample. Then there is a flip of `C` (`Flip C n`):
a normal integral, proper, Noetherian and projective $k$-scheme $X^+$ with a small proper morphism
$f^+ : X^+ → Y$ for which $\mathcal O_Y → f^+_*\mathcal O_{X^+}$ is an isomorphism, an isomorphism
between open subschemes of $X$ and $X^+$ compatible with the maps to $Y$, and a canonical module $ω$
of $X^+$ with a positive power whose double dual is a line bundle that is relatively ample over
$Y$. -/
def_wanted flip (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom]
    [IsNoetherian X.left]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (projective : ProjectiveSpace.IsProjective X)
    (hn : 3 ≤ n) (K : LineBundle X.left)
    (hK : SerreDualizingLine X.hom K.val n)
    (v : N1 X) (ray : IsExtremalRay v) (negative : v.val K < 0)
    (C : Contraction X v) (small : IsSmall C.map.left n)
    (Kinv : InverseLine K)
    (antiCanonical : IsRelativelyAmple C.map Kinv.inverse) : Flip C n

end WantedExt.AlgebraicGeometry.MoriConeContractionWanted
