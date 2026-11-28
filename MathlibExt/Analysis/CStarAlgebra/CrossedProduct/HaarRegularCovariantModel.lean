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

public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.PointwiseOperator
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarRegularRepresentation
public import MathlibExt.Analysis.CStarAlgebra.PointNormAction
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Haar regular covariant representation from a coefficient representation

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ:A→B(H) a nonunital complex star homomorphism. On K=L²(G,μ;H), let
Π(a)=regularCoefficientOperator α ρ μ a, given almost everywhere by
(Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). Together with (λ_g ξ)(s)=ξ(g⁻¹*s), these operators form a
covariant representation: λ_g Π(a) λ_g*=Π(α_g(a)). The pointwise coefficient operator is also
defined for regular measures before assuming Haar invariance.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped CStarAlgebra InnerProductSpace

namespace PointNormCStarAction

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : PointNormCStarAction G A) (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- **Inverse-action coefficient operator field.**

Let G be a topological group, A a nonunital complex C-star algebra, α a point-norm action on
A, H a complex Hilbert space and ρ:A→B(H) a nonunital complex star homomorphism. For a∈A,
regularCoefficientField α ρ a:G→B(H) is the field s↦ρ(α_(s⁻¹)(a)).
-/
def regularCoefficientField (a : A) : G → H →L[ℂ] H := fun s => ρ (α s⁻¹ a)

/-- **Joint vector continuity of the regular coefficient field.**

Let G be a topological group, A a nonunital complex C-star algebra, α a point-norm action on
A, H a complex Hilbert space and ρ:A→B(H) a nonunital complex star homomorphism. For a∈A, the
map (s,ξ)↦ρ(α_(s⁻¹)(a))ξ from G×H to H is continuous.
-/
theorem continuous_regularCoefficientField_action (a : A) :
    Continuous (fun z : G × H => regularCoefficientField α ρ a z.1 z.2) := by
  have hρ : Continuous (ρ : A → (H →L[ℂ] H)) := map_continuous ρ
  exact ((hρ.comp ((α.continuous_orbit a).comp continuous_inv)).comp
    continuous_fst).clm_apply continuous_snd

omit [IsTopologicalGroup G] in
/-- **Uniform norm bound for the regular coefficient field.**

Let G be a group with a topology, A a nonunital complex C-star algebra, α a point-norm action,
H a complex Hilbert space and ρ:A→B(H) a nonunital complex star homomorphism. For a∈A and s∈G,
‖regularCoefficientField α ρ a s‖=‖ρ(α_(s⁻¹)(a))‖≤‖a‖.
-/
theorem norm_regularCoefficientField_le (a : A) (s : G) :
    ‖regularCoefficientField α ρ a s‖ ≤ ‖a‖ := by
  change ‖ρ (α s⁻¹ a)‖ ≤ ‖a‖
  exact (NonUnitalStarAlgHom.norm_apply_le ρ (α s⁻¹ a)).trans (α.norm_apply s⁻¹ a).le

variable [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.Regular]

/-- **Pointwise regular coefficient operator on L².**

Let G be a locally compact Borel topological group, μ a regular measure, A a nonunital complex
C-star algebra, α a point-norm action, H a complex Hilbert space and ρ:A→B(H) a nonunital
complex star homomorphism. On K=L²(G,μ;H), let Π(a)=regularCoefficientOperator α ρ μ a, given
almost everywhere by (Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). The operator Π(a):K→L[ℂ]K is
regularCoefficientOperator α ρ μ a.
-/
def regularCoefficientOperator (a : A) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  HaarL2.pointwiseOperator (regularCoefficientField α ρ a)
    (continuous_regularCoefficientField_action α ρ a) μ ‖a‖
    (norm_regularCoefficientField_le α ρ a)

/-- **Almost-everywhere formula for the regular coefficient operator.**

Let G be a locally compact Borel topological group, μ a regular measure, A a nonunital complex
C-star algebra, α a point-norm action, H a complex Hilbert space and ρ:A→B(H) a nonunital
complex star homomorphism. On K=L²(G,μ;H), let Π(a)=regularCoefficientOperator α ρ μ a, given
almost everywhere by (Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). For a∈A and ξ∈K, regularCoefficientOperator
α ρ μ a ξ equals s↦ρ(α_(s⁻¹)(a))ξ(s) μ-almost everywhere.
-/
theorem regularCoefficientOperator_ae_eq (a : A) (ξ : Lp H 2 μ) :
    regularCoefficientOperator α ρ μ a ξ =ᵐ[μ] fun s : G => ρ (α s⁻¹ a) (ξ s) :=
  HaarL2.pointwiseOperator_ae_eq (regularCoefficientField α ρ a)
    (continuous_regularCoefficientField_action α ρ a) μ ‖a‖
    (norm_regularCoefficientField_le α ρ a) ξ

/-- **L² norm bound for regular coefficient multiplication.**

Let G be a locally compact Borel topological group, μ a regular measure, A a nonunital complex
C-star algebra, α a point-norm action, H a complex Hilbert space and ρ:A→B(H) a nonunital
complex star homomorphism. On K=L²(G,μ;H), let Π(a)=regularCoefficientOperator α ρ μ a, given
almost everywhere by (Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). For a∈A and ξ∈K, ‖Π(a)ξ‖≤‖a‖‖ξ‖.
-/
theorem norm_regularCoefficientOperator_apply_le (a : A) (ξ : Lp H 2 μ) :
    ‖regularCoefficientOperator α ρ μ a ξ‖ ≤ ‖a‖ * ‖ξ‖ :=
  HaarL2.pointwiseOperator_norm_apply_le (regularCoefficientField α ρ a)
    (continuous_regularCoefficientField_action α ρ a) μ ‖a‖
    (norm_regularCoefficientField_le α ρ a) ξ

/-- **Additivity of regular coefficient operators.**

Let G be a locally compact Borel topological group, μ a regular measure, A a nonunital complex
C-star algebra, α a point-norm action, H a complex Hilbert space and ρ:A→B(H) a nonunital
complex star homomorphism. On K=L²(G,μ;H), let Π(a)=regularCoefficientOperator α ρ μ a, given
almost everywhere by (Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). For a,b∈A, Π(a+b)=Π(a)+Π(b).
-/
theorem regularCoefficientOperator_add (a b : A) :
    regularCoefficientOperator α ρ μ (a + b) =
      regularCoefficientOperator α ρ μ a + regularCoefficientOperator α ρ μ b := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [regularCoefficientOperator_ae_eq α ρ μ (a + b) ξ,
    regularCoefficientOperator_ae_eq α ρ μ a ξ,
    regularCoefficientOperator_ae_eq α ρ μ b ξ,
    Lp.coeFn_add (regularCoefficientOperator α ρ μ a ξ) (regularCoefficientOperator α ρ μ b ξ)]
    with s h₁ h₂ h₃ h₄
  change regularCoefficientOperator α ρ μ (a + b) ξ s =
    (regularCoefficientOperator α ρ μ a ξ + regularCoefficientOperator α ρ μ b ξ) s
  rw [h₁, h₄, Pi.add_apply, h₂, h₃, map_add (α.aut s⁻¹), map_add ρ]
  rfl

/-- **Complex scaling of regular coefficient operators.**

Let G be a locally compact Borel topological group, μ a regular measure, A a nonunital complex
C-star algebra, α a point-norm action, H a complex Hilbert space and ρ:A→B(H) a nonunital
complex star homomorphism. On K=L²(G,μ;H), let Π(a)=regularCoefficientOperator α ρ μ a, given
almost everywhere by (Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). For c∈ℂ and a∈A, Π(c•a)=c•Π(a).
-/
theorem regularCoefficientOperator_smul (c : ℂ) (a : A) :
    regularCoefficientOperator α ρ μ (c • a) = c • regularCoefficientOperator α ρ μ a := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [regularCoefficientOperator_ae_eq α ρ μ (c • a) ξ,
    regularCoefficientOperator_ae_eq α ρ μ a ξ,
    Lp.coeFn_smul c (regularCoefficientOperator α ρ μ a ξ)] with s h₁ h₂ h₃
  change regularCoefficientOperator α ρ μ (c • a) ξ s =
    (c • regularCoefficientOperator α ρ μ a ξ) s
  rw [h₁, h₃, Pi.smul_apply, h₂, map_smul (α.aut s⁻¹), map_smul ρ]
  rfl

/-- **Multiplication of regular coefficient operators.**

Let G be a locally compact Borel topological group, μ a regular measure, A a nonunital complex
C-star algebra, α a point-norm action, H a complex Hilbert space and ρ:A→B(H) a nonunital
complex star homomorphism. On K=L²(G,μ;H), let Π(a)=regularCoefficientOperator α ρ μ a, given
almost everywhere by (Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). For a,b∈A, Π(a*b)=Π(a)*Π(b), where the
right product is operator composition.
-/
theorem regularCoefficientOperator_mul (a b : A) :
    regularCoefficientOperator α ρ μ (a * b) =
      regularCoefficientOperator α ρ μ a * regularCoefficientOperator α ρ μ b := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [regularCoefficientOperator_ae_eq α ρ μ (a * b) ξ,
    regularCoefficientOperator_ae_eq α ρ μ a (regularCoefficientOperator α ρ μ b ξ),
    regularCoefficientOperator_ae_eq α ρ μ b ξ] with s h₁ h₂ h₃
  change regularCoefficientOperator α ρ μ (a * b) ξ s =
    regularCoefficientOperator α ρ μ a (regularCoefficientOperator α ρ μ b ξ) s
  rw [h₁, h₂, h₃, map_mul (α.aut s⁻¹), map_mul ρ]
  rfl

/-- **Adjoint of a regular coefficient operator.**

Let G be a locally compact Borel topological group, μ a regular measure, A a nonunital complex
C-star algebra, α a point-norm action, H a complex Hilbert space and ρ:A→B(H) a nonunital
complex star homomorphism. On K=L²(G,μ;H), let Π(a)=regularCoefficientOperator α ρ μ a, given
almost everywhere by (Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). For a∈A, Π(star(a))=star(Π(a)), with
operator adjoint on K.
-/
theorem regularCoefficientOperator_star (a : A) :
    regularCoefficientOperator α ρ μ (star a) = star (regularCoefficientOperator α ρ μ a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff
    (regularCoefficientOperator α ρ μ (star a)) (regularCoefficientOperator α ρ μ a)).mpr
  intro ξ η
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularCoefficientOperator_ae_eq α ρ μ (star a) ξ,
    regularCoefficientOperator_ae_eq α ρ μ a η] with s h₁ h₂
  rw [h₁, h₂, StarHomClass.map_star (α.aut s⁻¹), StarHomClass.map_star ρ]
  change ⟪star (ρ (α s⁻¹ a)) (ξ s), η s⟫_ℂ = ⟪ξ s, ρ (α s⁻¹ a) (η s)⟫_ℂ
  rw [ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left (ρ (α s⁻¹ a)) (η s) (ξ s)

/-- **Regular coefficient star homomorphism.**

Let G be a locally compact Borel topological group, μ a regular measure, A a nonunital complex
C-star algebra, α a point-norm action, H a complex Hilbert space and ρ:A→B(H) a nonunital
complex star homomorphism. On K=L²(G,μ;H), let Π(a)=regularCoefficientOperator α ρ μ a, given
almost everywhere by (Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). The map regularCoefficientHom α ρ μ:A→B(K),
a↦Π(a), is a nonunital complex star homomorphism.
-/
def regularCoefficientHom : A →⋆ₙₐ[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) where
  toFun := regularCoefficientOperator α ρ μ
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply Lp.ext
    filter_upwards [regularCoefficientOperator_ae_eq α ρ μ (0 : A) ξ,
      Lp.coeFn_zero H 2 μ] with s h₁ h₂
    change regularCoefficientOperator α ρ μ (0 : A) ξ s = (0 : Lp H 2 μ) s
    rw [h₁, h₂, map_zero (α.aut s⁻¹), map_zero ρ]
    rfl
  map_add' := regularCoefficientOperator_add α ρ μ
  map_mul' := regularCoefficientOperator_mul α ρ μ
  map_smul' := regularCoefficientOperator_smul α ρ μ
  map_star' := regularCoefficientOperator_star α ρ μ

variable [μ.IsHaarMeasure]

/-- **Covariance of Haar regular coefficient and group operators.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ:A→B(H) a nonunital complex star homomorphism. On K=L²(G,μ;H), let
Π(a)=regularCoefficientOperator α ρ μ a, given almost everywhere by
(Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). For the left Haar regular unitary λ_g ξ(s)=ξ(g⁻¹*s),
λ_g*Π(a)*star(λ_g)=Π(α_g(a)) for g∈G and a∈A.
-/
theorem regularCoefficientOperator_covariance (g : G) (a : A) :
    (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) * regularCoefficientOperator α ρ μ a *
      star (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) = regularCoefficientOperator α ρ μ (α g a) := by
  rw [StronglyContinuousUnitaryRepresentation.star_haarLeftRegular]
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  let L (h : G) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
    StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H h
  let η := L g⁻¹ ξ
  have houter := StronglyContinuousUnitaryRepresentation.haarLeftRegular_ae_eq G μ H g
    (regularCoefficientOperator α ρ μ a η)
  have hcoefficient := regularCoefficientOperator_ae_eq α ρ μ a η
  have hinner := StronglyContinuousUnitaryRepresentation.haarLeftRegular_ae_eq G μ H g⁻¹ ξ
  have hpres : MeasurePreserving (fun s : G => g⁻¹ * s) μ μ := measurePreserving_smul g⁻¹ μ
  have hquasi : QuasiMeasurePreserving (fun s : G => g⁻¹ * s) μ μ :=
    ⟨hpres.measurable.aemeasurable, by rw [hpres.map_eq]⟩
  have hcoefficient' := hquasi.ae_eq_comp hcoefficient
  have hinner' := hquasi.ae_eq_comp hinner
  filter_upwards [houter, hcoefficient', hinner', regularCoefficientOperator_ae_eq α ρ μ (α g a) ξ]
    with s h₁ h₂ h₃ h₄
  change L g (regularCoefficientOperator α ρ μ a (L g⁻¹ ξ)) s =
    regularCoefficientOperator α ρ μ (α g a) ξ s
  simp only [Function.comp_apply] at h₂ h₃
  rw [h₁, h₂, h₃, h₄]
  simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left]
  exact congrArg (fun b : A => ρ b (ξ s)) (α.apply_mul s⁻¹ g a)

/-- **Haar regular covariant pair.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ:A→B(H) a nonunital complex star homomorphism. On K=L²(G,μ;H), let
Π(a)=regularCoefficientOperator α ρ μ a, given almost everywhere by
(Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). The pair regularCovariantRepresentation α ρ μ on K consists of Π
and the strongly continuous Haar left regular unitaries λ_g ξ(s)=ξ(g⁻¹*s).
-/
def regularCovariantRepresentation : CovariantRepresentation α (Lp H 2 μ) where
  algebra := regularCoefficientHom α ρ μ
  group := StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H
  covariance := by
    intro g a
    change (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) * regularCoefficientOperator α ρ μ a *
      star (StronglyContinuousUnitaryRepresentation.haarLeftRegular G μ H g :
        Lp H 2 μ →L[ℂ] Lp H 2 μ) = regularCoefficientOperator α ρ μ (α g a)
    exact regularCoefficientOperator_covariance α ρ μ g a

end

end PointNormCStarAction
