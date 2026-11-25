/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BetaDifferentialRingModels
public import MathlibExt.AlgebraicGeometry.DifferentialOperatorScalars

/-!
# Original complex constants of the native differential ring sheaf

The scalar map is fixed by multiplication by the original constant
coefficient function, followed by the actual sheafification unit. This
qualifies the complex algebra structure used for beta-D ring objects.
Source: DK1311.2374v2 Section 4.10; native scalar/operator APIs and
sheafification at Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DifferentialComplexScalarModels

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open DifferentialOperatorSheaves DifferentialOperatorScalars RingedComplexCoefficientModels

variable (M : Type) [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} ℂ)
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]

def differentialConstant (U : Opens M) (c : ℂ) :
    (differentialRing ℂ M O).obj.obj (op U) :=
  ((toSheafify (Opens.grothendieckTopology M) (operatorPresheaf ℂ M O)).app (op U)).hom
    (scalarFinite ℂ M O U (algebraMap ℂ (O.obj (op U)) c))

structure DifferentialComplexSource where
  scalar : ComplexRingSheafSource (TopCat.of M) (differentialRing ℂ M O)
  constants : ∀ (U : Opens M) (c : ℂ),
    letI := scalar
    letI : Algebra ℂ ((differentialRing ℂ M O).obj.obj (op U)) :=
      ComplexRingSheafSource.algebra (X := TopCat.of M) (R := differentialRing ℂ M O) U
    algebraMap ℂ ((differentialRing ℂ M O).obj.obj (op U)) c = differentialConstant M O U c

end MathlibExt.AlgebraicGeometry.DifferentialComplexScalarModels
