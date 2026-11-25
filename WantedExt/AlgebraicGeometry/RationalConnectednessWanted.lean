/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RationalCurveFamilies
public import MathlibExt.AlgebraicGeometry.PlurigenusFamilies

/-!
# Rational connectedness of smooth Fano varieties

The output is a genuine family of rational curves with dominant two-point
evaluation. The anti-canonical hypothesis uses an actual inverse to the
Serre-characterized canonical line and the coherent global-generation
criterion for ampleness. Birational invariance uses Mathlib's
`Scheme.BirationalOver`, a dense-open isomorphism over the field.

References: Campana, *Connexité rationnelle des variétés de Fano*,
Annales scientifiques de l'ENS 25 (1992), 539–545;
Kollár–Miyaoka–Mori, *Rational connectedness and boundedness of Fano
manifolds*, Journal of Differential Geometry 36 (1992), 765–779;
Kollár, *Rational Curves on Algebraic Varieties*, Chapter IV.

Very-free tangent criteria, separable characteristic-p variants, fibrations
and moduli of rational curves remain additional infrastructure interfaces.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.RationalConnectednessWanted

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open ProjectiveLineSystems PlurigenusFamilies RationalCurveFamilies

universe u

def_wanted fanoFamily (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X : Over (Spec (.of k))) [IsIntegral X.left] [IsProper X.hom] [IsNoetherian X.left]
    (n : ℕ) [SmoothOfRelativeDimension n X.hom]
    (projective : ProjectiveSpace.IsProjective X) (K : LineBundle X.left)
    (canonical : SerreDualizingLine X.hom K.val n) (Kinv : InverseLine K)
    (ample : IsAmpleLine Kinv.inverse) : RationalCurveFamily X

theorem_wanted birational_invariance (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (X Y : Over (Spec (.of k))) [IsIntegral X.left] [IsIntegral Y.left]
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom] [Smooth Y.hom]
    (projectiveX : ProjectiveSpace.IsProjective X) (projectiveY : ProjectiveSpace.IsProjective Y)
    (birational : Scheme.BirationalOver X.hom Y.hom) :
    IsRationallyConnected X ↔ IsRationallyConnected Y

end WantedExt.AlgebraicGeometry.RationalConnectednessWanted
