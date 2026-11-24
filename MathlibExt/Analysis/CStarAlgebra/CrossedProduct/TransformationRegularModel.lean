/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.PointNormAction.C0Translation
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarRegularCovariantModel
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarIntegratedForm
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.ZeroAtInftyOpen

/-!
# The actual scalar Haar transformation-group representation

Evaluation of C0(G) at the identity, followed by the canonical scalar operator
map on Complex, feeds the existing regular Haar construction. Its actual
L2 carrier is Lp Complex2mu. The coefficient action is literal multiplication
by a(s); the group action is inverse left translation. The given coefficient
evaluation is not required faithful, and no model is selected from a source
equivalence or compactness theorem.

The transformation compact-operator comparison remains a separate source
output. These are its genuine operator and Haar-integral constructors on
all original groups and zero coefficients, with the fixed Haar convention.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped ZeroAtInfty

noncomputable section

open MeasureTheory
open scoped CStarAlgebra InnerProductSpace

namespace PointNormCStarAction

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The original scalar coefficient representation evaluates exactly at the group identity. -/
def c0ScalarCoefficientRepresentation : C₀(G, ℂ) →⋆ₙₐ[ℂ] (ℂ →L[ℂ] ℂ) :=
  (StarAlgHom.ofId ℂ (ℂ →L[ℂ] ℂ)).toNonUnitalStarAlgHom.comp
    (ZeroAtInftyContinuousMap.evalAt (A := ℂ) 1)

omit [IsTopologicalGroup G] in
/-- Every scalar coefficient action has its exact original identity-evaluation value. -/
@[simp]
theorem c0ScalarCoefficientRepresentation_apply (a : C₀(G, ℂ)) (z : ℂ) :
    c0ScalarCoefficientRepresentation a z = a 1 * z := by
  change algebraMap ℂ (ℂ →L[ℂ] ℂ) (a 1) z = a 1 * z
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (mu : Measure G) [mu.Regular] [mu.IsHaarMeasure]

/-- The actual scalar Haar covariant pair for the original transformation action. -/
def transformationCovariantRepresentation :
    CovariantRepresentation (c0LeftTranslationAction (G := G)) (Lp ℂ 2 mu) :=
  regularCovariantRepresentation (c0LeftTranslationAction (G := G))
    c0ScalarCoefficientRepresentation mu

/-- Its actual coefficient operator is multiplication by the original C0 value at every Haar vector. -/
theorem transformationCoefficient_ae_eq (a : C₀(G, ℂ)) (xi : Lp ℂ 2 mu) :
    (transformationCovariantRepresentation mu).algebra a xi =ᵐ[mu]
      fun s : G => a s * xi s := by
  change (regularCoefficientOperator (c0LeftTranslationAction (G := G))
    c0ScalarCoefficientRepresentation mu a) xi =ᵐ[mu] (fun s : G => a s * xi s)
  simpa only [c0ScalarCoefficientRepresentation_apply, c0LeftTranslationAction_apply, inv_inv, mul_one] using
    regularCoefficientOperator_ae_eq (c0LeftTranslationAction (G := G))
      c0ScalarCoefficientRepresentation mu a xi

/-- Its actual group unitary is the original inverse left Haar translation. -/
theorem transformationGroup_ae_eq (g : G) (xi : Lp ℂ 2 mu) :
    ((transformationCovariantRepresentation mu).group g : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) xi =ᵐ[mu]
      fun s : G => xi (g⁻¹ * s) :=
  StronglyContinuousUnitaryRepresentation.haarLeftRegular_ae_eq G mu ℂ g xi

/-- The literal integrated original scalar transformation representation on the actual Haar core. -/
def transformationIntegratedHom :
    HaarTwistedCore.Carrier mu (c0LeftTranslationAction (G := G)) →⋆ₙₐ[ℂ]
      (Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) :=
  CovariantRepresentation.haarIntegratedHom mu (transformationCovariantRepresentation mu)

end PointNormCStarAction
