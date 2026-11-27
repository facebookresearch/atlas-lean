/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RubberModuliStackModels

/-!
# Actual rubber moduli and stabilization construction requests

Signed contact ideals, pure node equations, combined automorphisms,
Cartesian family reindexing, and marked-curve stabilization are fixed by
the native models. The requested stack has as fibres the stable rubber
families whose targets are framed fppf-locally on the base, including
twisted targets, so the fibre groupoids satisfy descent. The stable-range
and balanced signed contact are the source conditions for epsilon. Virtual
obstruction and Pixton comparison remain independent requests.
Source: JPPZ arXiv:1602.04705v2, Section0.2.4, printed p6;
Jun Li arXiv:math/0009097v1 and math/0110113v1;
Marcus–Wise arXiv:1310.5981, Sections 2.1–2.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.RubberModuliStackModelsWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open RelativeProjectiveLineModels ExpandedTargetChainGeometry StandardRelativeExpansionModels
open RubberMapFamilies RubberModuliStackModels StableCurveStackModels
open scoped BigOperators

def_wanted nativeRubberOriginalPair (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (O : ProjectiveLine (Spec (.of k)) (CoherentCurveLinearSeries.structureModule (Spec (.of k)))) :
    Σ P : RelativePair (k := k), OriginalRubberPair O P

def_wanted nativeRubberModuliStack (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (O : ProjectiveLine (Spec (.of k)) (CoherentCurveLinearSeries.structureModule (Spec (.of k))))
    (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
    (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
    {g n : ℕ} (a : Fin n → ℤ) (balanced : ∑ i, a i = 0) :
    RubberModuliModel O P D R S (g := g) a

def_wanted nativeRubberEpsilon (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (O : ProjectiveLine (Spec (.of k)) (CoherentCurveLinearSeries.structureModule (Spec (.of k))))
    (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
    (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
    {g n : ℕ} (a : Fin n → ℤ) (balanced : ∑ i, a i = 0) (stableRange : 2 * g + n > 2)
    (B : RubberModuliModel O P D R S (g := g) a) (M : StableCurveStackModel (k := k) g n) :
    EpsilonData O P D R S a B M

end WantedExt.AlgebraicGeometry.RubberModuliStackModelsWanted
