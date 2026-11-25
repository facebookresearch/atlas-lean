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
# Scalar Haar transformation-group representation

Let G be a locally compact Borel topological group and μ a regular left Haar measure. On
A=C₀(G,ℂ) take the point-norm action α_g(a)(s)=a(g⁻¹*s). The scalar transformation pair on
L²(G,μ;ℂ) is (M_a ξ)(s)=a(s)ξ(s), (λ_g ξ)(s)=ξ(g⁻¹*s), with formulas holding μ-almost
everywhere. This is the regular representation induced from coefficient evaluation a↦a(1) on
ℂ. For a compactly supported continuous coefficient F:G→C₀(G,ℂ), its integrated operator is
J(F)ξ=∫ t, M_(F(t))(λ_t ξ) ∂μ in L²(G,μ;ℂ).
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

/-- **Scalar coefficient representation by evaluation at the identity.**

Let G be a topological group. The nonunital complex star homomorphism
c0ScalarCoefficientRepresentation:C₀(G,ℂ)→B(ℂ) sends a to multiplication by a(1): z↦a(1)z.
-/
def c0ScalarCoefficientRepresentation : C₀(G, ℂ) →⋆ₙₐ[ℂ] (ℂ →L[ℂ] ℂ) :=
  (StarAlgHom.ofId ℂ (ℂ →L[ℂ] ℂ)).toNonUnitalStarAlgHom.comp
    (ZeroAtInftyContinuousMap.evalAt (A := ℂ) 1)

omit [IsTopologicalGroup G] in
/-- **Value of the identity-evaluation coefficient representation.**

Let G be a topological group, a∈C₀(G,ℂ) and z∈ℂ. Then c0ScalarCoefficientRepresentation a
z=a(1)*z.
-/
@[simp]
theorem c0ScalarCoefficientRepresentation_apply (a : C₀(G, ℂ)) (z : ℂ) :
    c0ScalarCoefficientRepresentation a z = a 1 * z := by
  change algebraMap ℂ (ℂ →L[ℂ] ℂ) (a 1) z = a 1 * z
  rw [Algebra.algebraMap_eq_smul_one]
  rfl

variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (mu : Measure G) [mu.Regular] [mu.IsHaarMeasure]

/-- **Covariant scalar transformation pair.**

Let G be a locally compact Borel topological group and μ a regular left Haar measure. On
A=C₀(G,ℂ) take the point-norm action α_g(a)(s)=a(g⁻¹*s). The scalar transformation pair on
L²(G,μ;ℂ) is (M_a ξ)(s)=a(s)ξ(s), (λ_g ξ)(s)=ξ(g⁻¹*s), with formulas holding μ-almost
everywhere. The pair transformationCovariantRepresentation μ=(M,λ) is a covariant
representation of α on L²(G,μ;ℂ).
-/
def transformationCovariantRepresentation :
    CovariantRepresentation (c0LeftTranslationAction (G := G)) (Lp ℂ 2 mu) :=
  regularCovariantRepresentation (c0LeftTranslationAction (G := G))
    c0ScalarCoefficientRepresentation mu

/-- **Transformation coefficient operator as multiplication.**

Let G be a locally compact Borel topological group and μ a regular left Haar measure. On
A=C₀(G,ℂ) take the point-norm action α_g(a)(s)=a(g⁻¹*s). For a∈C₀(G,ℂ) and ξ∈L²(G,μ;ℂ),
(transformationCovariantRepresentation μ).algebra a ξ equals s↦a(s)ξ(s) μ-almost everywhere.
-/
theorem transformationCoefficient_ae_eq (a : C₀(G, ℂ)) (xi : Lp ℂ 2 mu) :
    (transformationCovariantRepresentation mu).algebra a xi =ᵐ[mu]
      fun s : G => a s * xi s := by
  change (regularCoefficientOperator (c0LeftTranslationAction (G := G))
    c0ScalarCoefficientRepresentation mu a) xi =ᵐ[mu] (fun s : G => a s * xi s)
  simpa only [c0ScalarCoefficientRepresentation_apply, c0LeftTranslationAction_apply, inv_inv, mul_one] using
    regularCoefficientOperator_ae_eq (c0LeftTranslationAction (G := G))
      c0ScalarCoefficientRepresentation mu a xi

/-- **Transformation group operator as Haar translation.**

Let G be a locally compact Borel topological group and μ a regular left Haar measure. On
A=C₀(G,ℂ) take the point-norm action α_g(a)(s)=a(g⁻¹*s). For g∈G and ξ∈L²(G,μ;ℂ), the group
operator of transformationCovariantRepresentation μ at g sends ξ to s↦ξ(g⁻¹*s) μ-almost
everywhere.
-/
theorem transformationGroup_ae_eq (g : G) (xi : Lp ℂ 2 mu) :
    ((transformationCovariantRepresentation mu).group g : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) xi =ᵐ[mu]
      fun s : G => xi (g⁻¹ * s) :=
  StronglyContinuousUnitaryRepresentation.haarLeftRegular_ae_eq G mu ℂ g xi

/-- **Integrated scalar transformation homomorphism.**

Let G be a locally compact Borel topological group and μ a regular left Haar measure. On
A=C₀(G,ℂ) take the point-norm action α_g(a)(s)=a(g⁻¹*s). The scalar transformation pair on
L²(G,μ;ℂ) is (M_a ξ)(s)=a(s)ξ(s), (λ_g ξ)(s)=ξ(g⁻¹*s), with formulas holding μ-almost
everywhere. The nonunital complex star homomorphism transformationIntegratedHom μ from Carrier
μ α to B(L²(G,μ;ℂ)) sends a core coefficient F:G→C₀(G,ℂ) to J(F), where J(F)ξ=∫ t,
M_(F(t))(λ_t ξ) ∂μ as a Bochner integral in L².
-/
def transformationIntegratedHom :
    HaarTwistedCore.Carrier mu (c0LeftTranslationAction (G := G)) →⋆ₙₐ[ℂ]
      (Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) :=
  CovariantRepresentation.haarIntegratedHom mu (transformationCovariantRepresentation mu)

end PointNormCStarAction
