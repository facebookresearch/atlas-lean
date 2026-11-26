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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarRegularCovariantModel
public import MathlibExt.Analysis.InnerProductSpace.Group.HaarL2.CompactSupportFaithful
public import Mathlib.Analysis.CStarAlgebra.Hom

/-!
# Faithfulness of Haar regular coefficient operators

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ:A→B(H) a nonunital complex star homomorphism. On K=L²(G,μ;H), let
Π(a)=regularCoefficientOperator α ρ μ a, given almost everywhere by
(Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). If Π(a)=0, then ρ(a)=0. Hence injectivity of ρ implies
injectivity of a↦Π(a), and ‖Π(a)‖=‖a‖ for every a∈A.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped CompactlySupported CStarAlgebra

namespace PointNormCStarAction

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : PointNormCStarAction G A) (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
variable (μ : Measure G) [μ.Regular] [μ.IsHaarMeasure]

/-- **A zero regular coefficient operator has zero coefficient image.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ:A→B(H) a nonunital complex star homomorphism. On K=L²(G,μ;H), let
Π(a)=regularCoefficientOperator α ρ μ a, given almost everywhere by
(Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). For a∈A, regularCoefficientOperator α ρ μ a=0 implies ρ(a)=0.
-/
theorem regularCoefficientOperator_eq_zero_implies (a : A)
    (hZero : regularCoefficientOperator α ρ μ a = 0) : ρ a = 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  obtain ⟨ψ, hψcomp, _hψnonneg, hψone⟩ := exists_continuous_nonneg_pos (1 : G)
  let F : C_c(G, H) :=
    { toFun s := ((ψ s : ℝ) : ℂ) • ξ
      continuous_toFun :=
        (Complex.continuous_ofReal.comp ψ.continuous).smul continuous_const
      hasCompactSupport' := hψcomp.comp_left
        (g := fun r : ℝ => (r : ℂ) • ξ) (by simp) }
  let T := regularCoefficientField α ρ a
  let hT := continuous_regularCoefficientField_action α ρ a
  let J : C_c(G, H) := HaarL2.pointwiseCompactSupport T hT F
  have hImage : HaarL2.compactSupportInclusion μ J = 0 := by
    rw [← HaarL2.pointwiseOperator_apply_compactSupport T hT μ ‖a‖
      (norm_regularCoefficientField_le α ρ a) F]
    change regularCoefficientOperator α ρ μ a (HaarL2.compactSupportInclusion μ F) = 0
    rw [hZero]
    rfl
  have hJ : J = 0 := HaarL2.injective_compactSupportInclusion μ
    (hImage.trans (map_zero (HaarL2.compactSupportInclusion (H := H) μ)).symm)
  have hValue := congrArg (fun f : C_c(G, H) => f (1 : G)) hJ
  change ρ (α (1 : G)⁻¹ a) (((ψ (1 : G) : ℝ) : ℂ) • ξ) = 0 at hValue
  rw [inv_one, α.apply_one, map_smul] at hValue
  have hScalar : ((ψ (1 : G) : ℝ) : ℂ) ≠ 0 := by
    intro h
    apply hψone
    simpa using congrArg Complex.re h
  exact (smul_eq_zero.mp hValue).resolve_left hScalar

/-- **A faithful coefficient representation gives a faithful regular one.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ:A→B(H) a nonunital complex star homomorphism. On K=L²(G,μ;H), let
Π(a)=regularCoefficientOperator α ρ μ a, given almost everywhere by
(Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). If ρ is injective, then regularCoefficientHom α ρ μ:A→B(K),
a↦Π(a), is injective.
-/
theorem regularCoefficientHom_injective (hρ : Function.Injective ρ) :
    Function.Injective (regularCoefficientHom α ρ μ) := by
  intro a b hab
  apply hρ
  have hZero : regularCoefficientOperator α ρ μ (a - b) = 0 := by
    change regularCoefficientHom α ρ μ (a - b) = 0
    rw [map_sub, hab, sub_self]
  have hOriginal := regularCoefficientOperator_eq_zero_implies α ρ μ (a - b) hZero
  exact sub_eq_zero.mp (by simpa only [map_sub] using hOriginal)

/-- **Norm preservation of a faithful regular coefficient representation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let H be a complex
Hilbert space and ρ:A→B(H) a nonunital complex star homomorphism. On K=L²(G,μ;H), let
Π(a)=regularCoefficientOperator α ρ μ a, given almost everywhere by
(Π(a)ξ)(s)=ρ(α_(s⁻¹)(a))ξ(s). If ρ is injective, then ‖regularCoefficientHom α ρ μ a‖=‖a‖ for
a∈A.
-/
theorem norm_regularCoefficientHom (hρ : Function.Injective ρ) (a : A) :
    ‖regularCoefficientHom α ρ μ a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map (regularCoefficientHom α ρ μ)
    (regularCoefficientHom_injective α ρ μ hρ) a

end

end PointNormCStarAction
