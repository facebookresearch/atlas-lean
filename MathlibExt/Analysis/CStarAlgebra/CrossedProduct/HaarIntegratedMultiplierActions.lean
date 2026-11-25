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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarIntegratedForm
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.MultiplierActions

/-!
# Integrated coefficient and group multiplier actions

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ=(π,U) a covariant representation of α on H. For a compactly supported
continuous core coefficient f:G→A, write Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ. For L_a f(s)=a*f(s),
R_a f(s)=f(s)*α_s(a), L_g f(s)=α_g(f(g⁻¹*s)) and R_g f(s)=δ(g)•f(s*g⁻¹), integration gives
Iρ(L_a f)=π(a)Iρ(f), Iρ(R_a f)=Iρ(f)π(a), Iρ(L_g f)=U_g Iρ(f) and Iρ(R_g f)=Iρ(f)U_g. Here
δ(g)=Measure.modularCharacter g.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped CompactlySupported CStarAlgebra

namespace CovariantRepresentation

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable {α : PointNormCStarAction G A} (ρ : CovariantRepresentation α H)

/-- **Left coefficient multiplication under Haar integration.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ=(π,U) a covariant representation of α on H. For a compactly supported
continuous core coefficient f:G→A, write Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ. For a∈A and L_a
f(s)=a*f(s), Iρ(L_a f)=π(a)*Iρ(f).
-/
theorem haarIntegratedHom_coefficientLeft (a : A) (f : HaarTwistedCore.Carrier μ α) :
    haarIntegratedHom μ ρ (HaarTwistedCore.coefficientLeft μ α a f) =
      ρ.algebra a * haarIntegratedHom μ ρ f := by
  apply ContinuousLinearMap.ext
  intro ξ
  rw [haarIntegratedHom_apply_vector]
  change (∫ s : G, ρ.algebra (a * f s) ((ρ.group s : H →L[ℂ] H) ξ) ∂μ) =
    ρ.algebra a (haarIntegratedHom μ ρ f ξ)
  simp_rw [map_mul ρ.algebra]
  change (∫ s : G, ρ.algebra a (ρ.algebra (f s) ((ρ.group s : H →L[ℂ] H) ξ)) ∂μ) =
    ρ.algebra a (∫ s : G, ρ.algebra (f s) ((ρ.group s : H →L[ℂ] H) ξ) ∂μ)
  exact (ρ.algebra a).integral_comp_comm
    (StronglyContinuousUnitaryRepresentation.integratedVector_integrable μ ρ.group ρ.algebra
      (HaarTwistedCore.toCc μ α f) ξ)

/-- **Right coefficient multiplication under Haar integration.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ=(π,U) a covariant representation of α on H. For a compactly supported
continuous core coefficient f:G→A, write Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ. For a∈A and R_a
f(s)=f(s)*α_s(a), Iρ(R_a f)=Iρ(f)*π(a).
-/
theorem haarIntegratedHom_coefficientRight (a : A) (f : HaarTwistedCore.Carrier μ α) :
    haarIntegratedHom μ ρ (HaarTwistedCore.coefficientRight μ α a f) =
      haarIntegratedHom μ ρ f * ρ.algebra a := by
  apply ContinuousLinearMap.ext
  intro ξ
  rw [haarIntegratedHom_apply_vector]
  change (∫ s : G, ρ.algebra (f s * α s a) ((ρ.group s : H →L[ℂ] H) ξ) ∂μ) =
    haarIntegratedHom μ ρ f (ρ.algebra a ξ)
  rw [haarIntegratedHom_apply_vector]
  apply integral_congr_ae
  filter_upwards [] with s
  have hu : star (ρ.group s : H →L[ℂ] H) * (ρ.group s : H →L[ℂ] H) = 1 :=
    (ρ.group s).prop.1
  have hCov : ρ.algebra (α s a) * (ρ.group s : H →L[ℂ] H) =
      (ρ.group s : H →L[ℂ] H) * ρ.algebra a := by
    rw [← ρ.covariance s a]
    simp only [mul_assoc, hu, mul_one]
  have hOp : ρ.algebra (f s * α s a) * (ρ.group s : H →L[ℂ] H) =
      ρ.algebra (f s) * (ρ.group s : H →L[ℂ] H) * ρ.algebra a := by
    rw [map_mul ρ.algebra]
    simpa only [mul_assoc] using congrArg (fun T => ρ.algebra (f s) * T) hCov
  exact congrArg (fun T : H →L[ℂ] H => T ξ) hOp

/-- **Left group translation under Haar integration.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ=(π,U) a covariant representation of α on H. For a compactly supported
continuous core coefficient f:G→A, write Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ. For g∈G and L_g
f(s)=α_g(f(g⁻¹*s)), Iρ(L_g f)=U_g*Iρ(f).
-/
theorem haarIntegratedHom_groupLeft (g : G) (f : HaarTwistedCore.Carrier μ α) :
    haarIntegratedHom μ ρ (HaarTwistedCore.groupLeft μ α g f) =
      (ρ.group g : H →L[ℂ] H) * haarIntegratedHom μ ρ f := by
  apply ContinuousLinearMap.ext
  intro ξ
  rw [haarIntegratedHom_apply_vector]
  let K : G → H := fun s =>
    ρ.algebra (α g (f (g⁻¹ * s))) ((ρ.group s : H →L[ℂ] H) ξ)
  change (∫ s : G, K s ∂μ) = (ρ.group g : H →L[ℂ] H) (haarIntegratedHom μ ρ f ξ)
  calc
    _ = ∫ t : G, K (g * t) ∂μ := (integral_mul_left_eq_self (μ := μ) K g).symm
    _ = ∫ t : G, (ρ.group g : H →L[ℂ] H)
        (ρ.algebra (f t) ((ρ.group t : H →L[ℂ] H) ξ)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      have hu : star (ρ.group g : H →L[ℂ] H) * (ρ.group g : H →L[ℂ] H) = 1 :=
        (ρ.group g).prop.1
      have hCov : ρ.algebra (α g (f t)) * (ρ.group g : H →L[ℂ] H) =
          (ρ.group g : H →L[ℂ] H) * ρ.algebra (f t) := by
        rw [← ρ.covariance g (f t)]
        simp only [mul_assoc, hu, mul_one]
      simp only [K, inv_mul_cancel_left, ρ.group.apply_mul]
      exact congrArg (fun T : H →L[ℂ] H => T ((ρ.group t : H →L[ℂ] H) ξ)) hCov
    _ = (ρ.group g : H →L[ℂ] H)
        (∫ t : G, ρ.algebra (f t) ((ρ.group t : H →L[ℂ] H) ξ) ∂μ) :=
      (ρ.group g : H →L[ℂ] H).integral_comp_comm
        (StronglyContinuousUnitaryRepresentation.integratedVector_integrable μ ρ.group ρ.algebra
          (HaarTwistedCore.toCc μ α f) ξ)
    _ = _ := rfl

/-- **Modular right translation under Haar integration.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ=(π,U) a covariant representation of α on H. For a compactly supported
continuous core coefficient f:G→A, write Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ. For g∈G and R_g
f(s)=δ(g)•f(s*g⁻¹), with δ(g)=Measure.modularCharacter g, Iρ(R_g f)=Iρ(f)*U_g.
-/
theorem haarIntegratedHom_groupRight (g : G) (f : HaarTwistedCore.Carrier μ α) :
    haarIntegratedHom μ ρ (HaarTwistedCore.groupRight μ α g f) =
      haarIntegratedHom μ ρ f * (ρ.group g : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro ξ
  rw [haarIntegratedHom_apply_vector]
  let F : G → H := fun s =>
    ρ.algebra (f (s * g⁻¹)) ((ρ.group s : H →L[ℂ] H) ξ)
  change (∫ s : G, ρ.algebra (((Measure.modularCharacter g : ℝ) : ℂ) • f (s * g⁻¹))
    ((ρ.group s : H →L[ℂ] H) ξ) ∂μ) =
      haarIntegratedHom μ ρ f ((ρ.group g : H →L[ℂ] H) ξ)
  calc
    _ = ∫ s : G, (Measure.modularCharacter g : ℝ) • F s ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [map_smul]
      rfl
    _ = (Measure.modularCharacter g : ℝ) • ∫ s : G, F s ∂μ := integral_smul _ _
    _ = ∫ t : G, F (t * g) ∂μ := (integral_mul_right_modular μ F g).symm
    _ = ∫ t : G, ρ.algebra (f t)
        ((ρ.group t : H →L[ℂ] H) ((ρ.group g : H →L[ℂ] H) ξ)) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [F, mul_inv_cancel_right, ρ.group.apply_mul]
    _ = _ := rfl

/-- **Norm bound for integrated left coefficient multiplication.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ=(π,U) a covariant representation of α on H. For a compactly supported
continuous core coefficient f:G→A, write Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ. For a∈A and L_a
f(s)=a*f(s), ‖Iρ(L_a f)‖≤‖a‖‖Iρ(f)‖.
-/
theorem norm_haarIntegratedHom_coefficientLeft_le (a : A) (f : HaarTwistedCore.Carrier μ α) :
    ‖haarIntegratedHom μ ρ (HaarTwistedCore.coefficientLeft μ α a f)‖ ≤
      ‖a‖ * ‖haarIntegratedHom μ ρ f‖ := by
  rw [haarIntegratedHom_coefficientLeft]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (NonUnitalStarAlgHom.norm_apply_le ρ.algebra a) (norm_nonneg _))

/-- **Norm bound for integrated right coefficient multiplication.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ=(π,U) a covariant representation of α on H. For a compactly supported
continuous core coefficient f:G→A, write Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ. For a∈A and R_a
f(s)=f(s)*α_s(a), ‖Iρ(R_a f)‖≤‖Iρ(f)‖‖a‖.
-/
theorem norm_haarIntegratedHom_coefficientRight_le (a : A) (f : HaarTwistedCore.Carrier μ α) :
    ‖haarIntegratedHom μ ρ (HaarTwistedCore.coefficientRight μ α a f)‖ ≤
      ‖haarIntegratedHom μ ρ f‖ * ‖a‖ := by
  rw [haarIntegratedHom_coefficientRight]
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_left (NonUnitalStarAlgHom.norm_apply_le ρ.algebra a) (norm_nonneg _))

/-- **Integrated norm is invariant under left group translation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ=(π,U) a covariant representation of α on H. For a compactly supported
continuous core coefficient f:G→A, write Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ. For g∈G and L_g
f(s)=α_g(f(g⁻¹*s)), ‖Iρ(L_g f)‖=‖Iρ(f)‖.
-/
theorem norm_haarIntegratedHom_groupLeft (g : G) (f : HaarTwistedCore.Carrier μ α) :
    ‖haarIntegratedHom μ ρ (HaarTwistedCore.groupLeft μ α g f)‖ =
      ‖haarIntegratedHom μ ρ f‖ := by
  rw [haarIntegratedHom_groupLeft]
  exact CStarRing.norm_coe_unitary_mul (ρ.group g) (haarIntegratedHom μ ρ f)

/-- **Integrated norm is invariant under right group translation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ=(π,U) a covariant representation of α on H. For a compactly supported
continuous core coefficient f:G→A, write Iρ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ. For g∈G and R_g
f(s)=δ(g)•f(s*g⁻¹), with δ(g)=Measure.modularCharacter g, ‖Iρ(R_g f)‖=‖Iρ(f)‖.
-/
theorem norm_haarIntegratedHom_groupRight (g : G) (f : HaarTwistedCore.Carrier μ α) :
    ‖haarIntegratedHom μ ρ (HaarTwistedCore.groupRight μ α g f)‖ =
      ‖haarIntegratedHom μ ρ f‖ := by
  rw [haarIntegratedHom_groupRight]
  exact CStarRing.norm_mul_coe_unitary (haarIntegratedHom μ ρ f) (ρ.group g)

end

end CovariantRepresentation
