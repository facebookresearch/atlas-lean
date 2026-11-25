/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

@[expose] public section

/-!
# Brill--Noether nonemptiness

For every smooth proper integral curve over an algebraically closed
characteristic-zero field, nonnegative Brill--Noether number guarantees a
linear series. No generic-curve predicate is used. The imported completed
interface uses actual module-sheaf cohomology.

The hypotheses are the standard ones: the curve is a proper curve in the sense
of `IsProperCurve` because it is smooth of relative dimension one, and its genus
is defined because an integral proper scheme over an algebraically closed field
has only constant global functions (`HasConstantGlobalSections.of_isIntegral`).

Sources: G. Kempf, *Schubert methods with an application to algebraic
curves* (1971); S. Kleiman and D. Laksov, *On the existence of special
divisors*, Amer. J. Math. 94 (1972), 431--436; ACGH, *Geometry of Algebraic
Curves I*, Chapter V. https://doi.org/10.2307/2374630
-/

namespace WantedExt.AlgebraicGeometry.BrillNoetherExistence

open CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u

/-- **Existence of linear series with nonnegative Brill–Noether number.** Kempf, Kleiman–Laksov:
let $k$ be an algebraically closed field of characteristic zero and $C$ an integral proper
$k$-scheme, smooth of relative dimension one, of genus $g = \dim_k H^1(C, \mathcal{O}_C)$. If
$d, r \in \mathbb{N}$ satisfy $\rho(g, r, d) = g - (r + 1)(g - d + r) \ge 0$, then $C$ carries a
linear series $g^r_d$: a line bundle of degree $d$ with an $(r + 1)$-dimensional subspace of its
global sections. -/
public theorem_wanted brillNoether_nonempty
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (C : Over (Spec (.of k))) [IsIntegral C.left] [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom]
    (d r : ℕ) (hρ : 0 ≤ brillNoetherNumber (genus C.hom) d r) :
    Nonempty (LinearSeries C.hom d r)

end WantedExt.AlgebraicGeometry.BrillNoetherExistence
