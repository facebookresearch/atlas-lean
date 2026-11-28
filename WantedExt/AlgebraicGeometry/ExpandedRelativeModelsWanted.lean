/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ExpandedRelativeFamilies

/-!
# Native projective-line and standard relative-expansion construction requests

The relative normal line, actual subline functor, coordinate boundaries,
blowup center, schematic strict transform, parameter torus, scalar ratios,
special-fibre quotient and every family/base-change map are already fixed
in MathlibExt. These constructors assemble the native source models.
They assume no relative or rubber GW virtual-cycle identity.
Sources: Jun Li arXiv:math/0009097v1, Sections1 and4;
arXiv:math/0110113v1, Sections1--3.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ExpandedRelativeModelsWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeProjectiveLineModels ExpandedTargetChainGeometry
open ExpansionParameterModels StandardRelativeExpansionModels ExpansionScalingModels ExpandedRelativeFamilies

def_wanted nativeRelativeProjectiveLine (D : Scheme.{0}) (N : D.Modules) (line : IsLineBundle N) :
    ProjectiveLine D N

def_wanted nativeExpansionTorus (k : Type) [Field k] (m : ℕ) : TorusTheory k m

def_wanted nativeRuledExpansionFibre (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P : RelativePair (k := k)) (R : ProjectiveLine P.divisor.left (normalLineModule P)) (m : ℕ) :
    ExpandedSpecialFibre P R m

def_wanted nativeStandardRelativeExpansions (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P : RelativePair (k := k)) (R : ProjectiveLine P.divisor.left (normalLineModule P)) : StandardSystem P R

def_wanted nativeStandardExpansionScaling (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P : RelativePair (k := k)) (R : ProjectiveLine P.divisor.left (normalLineModule P))
    (S : StandardSystem P R) (m : ℕ) (H : TorusTheory k m) : ScalingData P R S m H

def_wanted nativeExpandedFamily (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P : RelativePair (k := k)) (R : ProjectiveLine P.divisor.left (normalLineModule P))
    (S : StandardSystem P R) (T : Over (Spec (.of k))) (m : ℕ) (f : T ⟶ ParameterSpace k m) :
    Σ F : ExpandedFamily P R S T, StandardFamilyIdentification P R S F m f

def_wanted nativeExpandedFamilyReindex (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
    (P : RelativePair (k := k)) (R : ProjectiveLine P.divisor.left (normalLineModule P))
    (S : StandardSystem P R) {T U : Over (Spec (.of k))} (f : T ⟶ U)
    (F : ExpandedFamily P R S U) : ExpandedReindex P R S f F

end WantedExt.AlgebraicGeometry.ExpandedRelativeModelsWanted
