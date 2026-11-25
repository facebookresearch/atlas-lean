/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.AbelianArithmeticHeights

/-!
# General abelian Néron–Tate height from actual projective geometry

Construct the canonical height for a symmetric very ample line on the
actual number-field abelian variety. The defining limit uses its actual
K-points, group multiplication and normalized projective-coordinate height.
No arbitrary height function or duplication-error bound is an input.

References: Gregory S. Call–Joseph H. Silverman, *Canonical heights on
varieties with morphisms*, Theorem 1.1 and Example 1, pp. 166–167;
Proposition 1.2, p. 169, gives the defining limit.
https://www.numdam.org/item/CM_1993__89_2_163_0.pdf
Hindry–Silverman, *Diophantine Geometry*, §B.5, for quadraticity and
positivity of the Néron–Tate height attached to an ample symmetric line.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.AbelianArithmeticHeights

open CategoryTheory CategoryTheory.MonObj _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AbelianArithmeticHeights

/-- Canonical normalized quadratic height of the actual abelian variety. -/
public def_wanted neronTateHeight
    (K : Type) [Field K] [NumberField K]
    (A : Over (Spec (CommRingCat.of.{0} K))) [GrpObj A] [IsCommMonObj A]
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    (M : SymmetricProjectiveModel A) : M.CanonicalHeight

end WantedExt.AlgebraicGeometry.AbelianArithmeticHeights
