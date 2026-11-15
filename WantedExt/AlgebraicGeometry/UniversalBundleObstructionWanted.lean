/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Data.Int.GCD
public import MathlibExt.AlgebraicGeometry.UniversalBundleObstruction

@[expose] public section

/-!
# The noncoprime universal stable-bundle obstruction

Authors: P. E. Newstead; S. Ramanan; I. Biswas, L. Brambila-Paz,
P. E. Newstead.

Sources: Newstead, *A non-existence theorem for families of stable
bundles*, J. London Math. Soc. 6 (1973), 259--266; Ramanan, *The moduli
spaces of vector bundles over an algebraic curve*, Math. Ann. 200
(1973), 69--84, https://eudml.org/doc/162339.
The obstruction and the projective universal replacement are stated
explicitly in the Introduction and §2 of Biswas--Brambila-Paz--Newstead,
https://arxiv.org/abs/0805.4131v3.

The unfixed-determinant version follows by restriction to the
fixed-determinant stable moduli. Rank and degree have a common divisor
greater than one. The model has no properness hypothesis, and the
question concerns the actual global universal vector bundle, retaining
the allowed base line-bundle ambiguity. Generic banded gerbes, their
cohomology and projective connecting maps are already available in
Axiom's Stacks formalization and are not requested here.
-/

namespace WantedExt.AlgebraicGeometry.UniversalBundleObstruction

open CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.UniversalBundleObstruction

/-- Noncoprime rank and degree obstruct a global universal stable family
on the stable moduli of a smooth complex curve of genus at least three. -/
public theorem_wanted noGlobalUniversalStableFamily
    (C : Over (Spec (.of ℂ))) [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (hgenus : 3 ≤ genus C.hom) (r : ℕ) (hr : 0 < r) (d : ℤ)
    (noncoprime : 1 < Nat.gcd r d.natAbs) :
    ¬ Nonempty (GlobalUniversalStableFamily C r d)

end WantedExt.AlgebraicGeometry.UniversalBundleObstruction

