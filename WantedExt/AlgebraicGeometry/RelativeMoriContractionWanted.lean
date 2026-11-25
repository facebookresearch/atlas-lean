/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RelativeProjectivity
public import MathlibExt.AlgebraicGeometry.RelativeMoriContracts

/-!
# Minimal general relative log-Mori proof contracts

The source is a normal real-boundary log pair with actual K+Delta Cartier
data. Its numerical cone uses genuine curves contracted over the given
base. Relative generation is the native pullback/pushforward counit.
Outputs are actual scheme maps, connected fibres and strict-transform
boundary/canonical flip data. Shared model calculus and representative
comparisons are explicit dependencies; smooth absolute statements are
preserved separately.

References: Kollár--Mori, *Birational Geometry of Algebraic Varieties*,
Chapter3 (relative cone, base-point-free and contraction theorems);
Birkar--Cascini--Hacon--McKernan, *Existence of minimal models for varieties
of log general type*, Corollary1.4.1 (klt flips).
No unrestricted termination, abundance or conjectural model constructor
is asserted.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RelativeMoriContractionWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.RelativeMoriContracts
open MathlibExt.AlgebraicGeometry.MoriContractionModels
open MathlibExt.AlgebraicGeometry.NumericalCurveCones
open MathlibExt.AlgebraicGeometry.RelativeProjectivity
open scoped BigOperators

universe u

/-- The degree on curves of a real combination of Cartier divisors depends only on its Weil divisor:
for a field $k$ of characteristic zero, a normal variety $V$ over $k$ and real combinations $D$ and
$E$ of Cartier divisors on $V$ with the same real Weil divisor, $D·C = E·C$ for every curve
$C → V$. -/
public theorem_wanted representative_curve_degree (k : Type u) [Field k] [CharZero k]
    (n : ℕ) (V : NormalVariety k n) (D E : CartierCombination V)
    (same : D.divisor = E.divisor) (C : Curve V.X) :
    combinationOnCurve D C = combinationOnCurve E C

/-- Finite dimensionality of relative numerical curve classes: let $k$ be an algebraically closed
field of characteristic zero, $(X, Δ)$ a log pair over $k$, $S$ a quasi-projective $k$-scheme (one
with an immersion into a projective space) and $q : X → S$ a projective morphism (a closed immersion
into $\mathbb P^N × S$ over $S$). Then the real span $N_1(X/S)$ of the classes of the curves
contracted by $q$ is finite-dimensional. -/
public theorem_wanted relative_numerical_finite (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (P : LogPair k n) (S : Over (Spec (.of k)))
    (base : IsQuasiProjectiveBase S) (q : P.variety.X ⟶ S) (projective : IsHProjectiveOver q) :
    FiniteDimensional ℝ (RelativeN1 q)

/-- The relative base-point-free theorem for klt pairs: let $k$ be an algebraically closed field of
characteristic zero, $(X, Δ)$ a klt log pair over $k$, $S$ a quasi-projective $k$-scheme and
$q : X → S$ a projective morphism. Let $L$ be a Cartier divisor on $X$, with its line bundle, that
is nef over $S$ (nonnegative degree on every curve contracted by $q$), $a > 0$ a natural number and
$D$ a real combination of Cartier divisors with Weil divisor $aL - (K_X + Δ)$ that is ample over
$S$. Then $L$ is semiample over $S$: for some $m > 0$ the evaluation map $q^*q_*L^{⊗ m} → L^{⊗ m}$
is an epimorphism. -/
public theorem_wanted relative_basepoint_free (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (P : LogPair k n) (klt : IsKlt P)
    (S : Over (Spec (.of k))) (base : IsQuasiProjectiveBase S)
    (q : P.variety.X ⟶ S) (projective : IsHProjectiveOver q)
    (L : CartierLine P.variety) (nef : ∀ C : Curve P.variety.X, IsContracted q C →
      0 ≤ curveDegrees C L.line)
    (a : ℕ) (positive : 0 < a) (D : CartierCombination P.variety)
    (normalized : D.divisor = (a : ℝ) • realCast L.divisor - P.adjoint.divisor)
    (ample : IsRelativelyAmpleR q D) : IsRelativelySemiample q L.line

/-- The relative contraction theorem for klt pairs: let $k$ be an algebraically closed field of
characteristic zero, $(X, Δ)$ a klt log pair over $k$ with $X$ ℚ-factorial, $S$ a quasi-projective
$k$-scheme, $q : X → S$ a projective morphism and $v$ a class spanning an extremal ray of the
relative cone of curves of $q$ with $(K_X + Δ)·v < 0$. Then there is a contraction of $v$ over $S$
(`RelativeContraction P q v`): a normal integral Noetherian $k$-scheme $Y$, projective over $S$, and
a proper projective morphism $f : X → Y$ over $S$ with geometrically connected fibres, for which
$\mathcal O_Y → f_*\mathcal O_X$ is an isomorphism, and which contracts a curve contracted by $q$
exactly when its class lies on the ray spanned by $v$. -/
public def_wanted relative_contraction (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (P : LogPair k n) (klt : IsKlt P)
    (qfactorial : IsQFactorial P.variety) (S : Over (Spec (.of k)))
    (base : IsQuasiProjectiveBase S) (q : P.variety.X ⟶ S) (projective : IsHProjectiveOver q)
    (v : RelativeN1 q) (extremal : IsExtremal v)
    (negative : combinationOnClass q P.adjoint v < 0) : RelativeContraction P q v

/-- Existence of klt flips (Birkar–Cascini–Hacon–McKernan, Corollary 1.4.1): let $k$ be an
algebraically closed field of characteristic zero, $(X, Δ)$ a klt log pair of dimension $n ≥ 3$ over
$k$ with $X$ ℚ-factorial, $S$ a quasi-projective $k$-scheme, $q : X → S$ a projective morphism, $v$
a class spanning an extremal ray of the relative cone of curves of $q$ with $(K_X + Δ)·v < 0$, and
`C` a small contraction of $v$ over $S$, with target $Y$, such that $-(K_X + Δ)$ is ample over $Y$.
Then there is a flip of `C` (`RelativeFlip C`): a klt log pair $(X^+, Δ^+)$ with $X^+$ ℚ-factorial,
a small proper projective morphism $f^+ : X^+ → Y$ for which $\mathcal O_Y → f^+_*\mathcal O_{X^+}$
is an isomorphism, and an isomorphism between open subschemes of $X$ and $X^+$ containing all
codimension-one points and compatible with the maps to $Y$, under which $Δ^+$ is the strict
transform of $Δ$, such that $K_{X^+} + Δ^+$ is ample over $Y$. -/
public def_wanted relative_flip (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (dimension : 3 ≤ n) (P : LogPair k n)
    (klt : IsKlt P) (qfactorial : IsQFactorial P.variety)
    (S : Over (Spec (.of k))) (base : IsQuasiProjectiveBase S)
    (q : P.variety.X ⟶ S) (projective : IsHProjectiveOver q)
    (v : RelativeN1 q) (extremal : IsExtremal v)
    (negative : combinationOnClass q P.adjoint v < 0) (C : RelativeContraction P q v)
    (small : IsSmall C.map.left n)
    (antiAdjoint : IsRelativelyAmpleR C.map (negativeCombination P.adjoint)) : RelativeFlip C

end WantedExt.AlgebraicGeometry.RelativeMoriContractionWanted
