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

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.GramCovariantRepresentation
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.ConvolutionSeminormIntegral
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarIntegratedForm
public import MathlibExt.Analysis.CStarAlgebra.SeminormHilbertModel
public import MathlibExt.Analysis.CStarAlgebra.EssentialNondegeneracy
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integrated identity for a Gram covariant representation

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the core satisfying p(k)≤∫ s, ‖k(s)‖ ∂μ for every core coefficient k, Xp its
separated completion and ιp its dense map. Let H be a complex Hilbert space and ρ:Xp→B(H) a
nonunital complex star homomorphism. Write E for its essential Hilbert subspace, ρE for the
restricted representation and T(f)=ρE(ιp(f)). The Gram coefficient and group operators P_a,U_g
on E satisfy P_a(T(f)ξ)=T(s↦a*f(s))ξ and U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For the Gram
covariant pair (P,U), put I(f)ξ=∫ s, P_(f(s))(U_s ξ) ∂μ. The integrated homomorphism satisfies
I(f)=T(f). If ρ is injective, then ‖I(f)‖=p(f). The coefficient representation P is
nondegenerate, so every L¹-dominated C-star seminorm has a nondegenerate covariant realization
with exactly its integrated norm.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped CStarAlgebra InnerProductSpace

namespace HaarTwistedCore

noncomputable section

universe uG uA uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
  (α : PointNormCStarAction G A)

attribute [local instance] CStarSeminorm.nonUnitalCompletionCStarAlgebra

variable (p : CStarSeminorm (Carrier μ α))

section HilbertModel

variable (H : Type uH)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (ρ : p.NonUnitalCompletion →⋆ₙₐ[ℂ] (H →L[ℂ] H))

/-- **Integrated Gram action on a source generator.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the core satisfying p(k)≤∫ s, ‖k(s)‖ ∂μ for every core coefficient k, Xp its
separated completion and ιp its dense map. Let H be a complex Hilbert space and ρ:Xp→B(H) a
nonunital complex star homomorphism. Write E for its essential Hilbert subspace, ρE for the
restricted representation and T(f)=ρE(ιp(f)). The Gram coefficient and group operators P_a,U_g
on E satisfy P_a(T(f)ξ)=T(s↦a*f(s))ξ and U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For the Gram
covariant pair (P,U), put I(f)ξ=∫ s, P_(f(s))(U_s ξ) ∂μ. For core coefficients f,h and ξ∈E,
I(f)(T(h)ξ)=T(f*h)ξ.
-/
theorem gramCovariant_haarIntegratedHom_apply_generator
    (hp : p ∈ admissibleCStarSeminorms μ α) (f h : Carrier μ α) (ξ : ρ.essentialSpace) :
    CovariantRepresentation.haarIntegratedHom μ (gramCovariantRepresentation μ α p H ρ hp) f
        (ρ.essentialRepresentation (p.toNonUnitalCompletion h) ξ) =
      ρ.essentialRepresentation (p.toNonUnitalCompletion (f * h)) ξ := by
  let _ : NormedSpace ℝ p.NonUnitalCompletion := NormedSpace.restrictScalars ℝ ℂ _
  let _ : NormedSpace ℝ ρ.essentialSpace := NormedSpace.restrictScalars ℝ ℂ _
  let σ : p.NonUnitalCompletion →L[ℂ] (ρ.essentialSpace →L[ℂ] ρ.essentialSpace) :=
    ⟨LinearMap.ofClass ρ.essentialRepresentation, map_continuous ρ.essentialRepresentation⟩
  let T : p.NonUnitalCompletion →L[ℂ] ρ.essentialSpace :=
    (ContinuousLinearMap.apply ℂ ρ.essentialSpace ξ).comp σ
  have hT (a : p.NonUnitalCompletion) : T a = ρ.essentialRepresentation a ξ := rfl
  let π := gramCovariantRepresentation μ α p H ρ hp
  have hValues (s : G) :
      π.algebra (f s) ((π.group s : ρ.essentialSpace →L[ℂ] ρ.essentialSpace)
        (ρ.essentialRepresentation (p.toNonUnitalCompletion h) ξ)) =
      T (p.toNonUnitalCompletion (coefficientLeft μ α (f s) (groupLeft μ α s h))) := by
    change gramCoefficientOperator μ α p H ρ (f s)
      (gramGroupOperator μ α p H ρ s (ρ.essentialRepresentation (p.toNonUnitalCompletion h) ξ)) = _
    rw [gramGroupOperator_apply_generator, gramCoefficientOperator_apply_generator, hT]
  calc
    _ = ∫ s : G, π.algebra (f s)
          ((π.group s : ρ.essentialSpace →L[ℂ] ρ.essentialSpace)
            (ρ.essentialRepresentation (p.toNonUnitalCompletion h) ξ)) ∂μ :=
      CovariantRepresentation.haarIntegratedHom_apply_vector μ π f _
    _ = ∫ s : G, T (p.toNonUnitalCompletion (coefficientLeft μ α (f s) (groupLeft μ α s h))) ∂μ :=
      integral_congr_ae (Eventually.of_forall hValues)
    _ = T (∫ s : G, p.toNonUnitalCompletion (coefficientLeft μ α (f s) (groupLeft μ α s h)) ∂μ) :=
      T.integral_comp_comm (integrable_toNonUnitalCompletion_coefficientLeft_groupLeft μ α p hp f h)
    _ = T (p.toNonUnitalCompletion (f * h)) := by
      rw [integral_toNonUnitalCompletion_coefficientLeft_groupLeft μ α p hp f h]
    _ = _ := hT _

/-- **Integrated Gram homomorphism equals the completed representation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the core satisfying p(k)≤∫ s, ‖k(s)‖ ∂μ for every core coefficient k, Xp its
separated completion and ιp its dense map. Let H be a complex Hilbert space and ρ:Xp→B(H) a
nonunital complex star homomorphism. Write E for its essential Hilbert subspace, ρE for the
restricted representation and T(f)=ρE(ιp(f)). The Gram coefficient and group operators P_a,U_g
on E satisfy P_a(T(f)ξ)=T(s↦a*f(s))ξ and U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For the Gram
covariant pair (P,U), put I(f)ξ=∫ s, P_(f(s))(U_s ξ) ∂μ. For each core coefficient f,
CovariantRepresentation.haarIntegratedHom μ (gramCovariantRepresentation μ α p H ρ hp)
f=T(f)=ρE(ιp(f)).
-/
theorem gramCovariant_haarIntegratedHom
    (hp : p ∈ admissibleCStarSeminorms μ α) (f : Carrier μ α) :
    CovariantRepresentation.haarIntegratedHom μ (gramCovariantRepresentation μ α p H ρ hp) f =
      ρ.essentialRepresentation (p.toNonUnitalCompletion f) := by
  apply gramOperator_ext μ α p H ρ
  intro h ξ
  rw [gramCovariant_haarIntegratedHom_apply_generator μ α p H ρ hp f h ξ]
  have hProduct : ρ.essentialRepresentation (p.toNonUnitalCompletion (f * h)) =
      ρ.essentialRepresentation (p.toNonUnitalCompletion f) *
        ρ.essentialRepresentation (p.toNonUnitalCompletion h) := by
    rw [map_mul, map_mul]
  rw [hProduct]
  rfl

/-- **Faithful Gram realization preserves a C-star seminorm.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the core satisfying p(k)≤∫ s, ‖k(s)‖ ∂μ for every core coefficient k, Xp its
separated completion and ιp its dense map. Let H be a complex Hilbert space and ρ:Xp→B(H) a
nonunital complex star homomorphism. Write E for its essential Hilbert subspace, ρE for the
restricted representation and T(f)=ρE(ιp(f)). The Gram coefficient and group operators P_a,U_g
on E satisfy P_a(T(f)ξ)=T(s↦a*f(s))ξ and U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For the Gram
covariant pair (P,U), put I(f)ξ=∫ s, P_(f(s))(U_s ξ) ∂μ. If ρ:Xp→B(H) is injective, then
‖I(f)‖=p(f) for every core coefficient f.
-/
theorem norm_gramCovariant_haarIntegratedHom
    (hp : p ∈ admissibleCStarSeminorms μ α) (hρ : Function.Injective ρ) (f : Carrier μ α) :
    ‖CovariantRepresentation.haarIntegratedHom μ (gramCovariantRepresentation μ α p H ρ hp) f‖ =
      p f := by
  rw [gramCovariant_haarIntegratedHom μ α p H ρ hp f,
    ρ.norm_essentialRepresentation hρ, p.norm_toNonUnitalCompletion]

/-- **Essential coefficient space of the Gram pair is the whole space.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the core satisfying p(k)≤∫ s, ‖k(s)‖ ∂μ for every core coefficient k, Xp its
separated completion and ιp its dense map. Let H be a complex Hilbert space and ρ:Xp→B(H) a
nonunital complex star homomorphism. Write E for its essential Hilbert subspace, ρE for the
restricted representation and T(f)=ρE(ιp(f)). The Gram coefficient and group operators P_a,U_g
on E satisfy P_a(T(f)ξ)=T(s↦a*f(s))ξ and U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. For the coefficient
representation P of gramCovariantRepresentation μ α p H ρ hp, closure(span_ℂ{P_a
ξ:a∈A,ξ∈E})=E; equivalently its essentialSpace is the whole Hilbert space.
-/
theorem gramCovariantRepresentation_essentialSpace_eq_top
    (hp : p ∈ admissibleCStarSeminorms μ α) :
    (gramCovariantRepresentation μ α p H ρ hp).algebra.essentialSpace = ⊤ := by
  let π := gramCovariantRepresentation μ α p H ρ hp
  let S : Submodule ℂ ρ.essentialSpace :=
    Submodule.span ℂ (Set.range fun z : A × ρ.essentialSpace => π.algebra z.1 z.2)
  let P : Submodule ℂ ρ.essentialSpace := S.topologicalClosure
  let _ : CompleteSpace P := S.isClosed_topologicalClosure.completeSpace_coe
  let _ : NormedSpace ℝ P := NormedSpace.restrictScalars ℝ ℂ _
  let _ : NormedSpace ℝ ρ.essentialSpace := NormedSpace.restrictScalars ℝ ℂ _
  have hValues (f : Carrier μ α) (ξ : ρ.essentialSpace) :
      ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ ∈ P := by
    let Ψ : G → P := fun s =>
      ⟨π.algebra (f s) ((π.group s : ρ.essentialSpace →L[ℂ] ρ.essentialSpace) ξ),
        S.le_topologicalClosure (Submodule.subset_span
          ⟨(f s, (π.group s : ρ.essentialSpace →L[ℂ] ρ.essentialSpace) ξ), rfl⟩)⟩
    have hContinuous : Continuous Ψ :=
      (((map_continuous π.algebra).comp (toCc μ α f).continuous).clm_apply
        (π.group.continuous_orbit ξ)).subtype_mk _
    have hSupport : HasCompactSupport Ψ := by
      apply hasCompactSupport_iff_eventuallyEq.mpr
      filter_upwards [hasCompactSupport_iff_eventuallyEq.mp (toCc μ α f).hasCompactSupport] with s hs
      apply Subtype.ext
      change π.algebra (f s) ((π.group s : ρ.essentialSpace →L[ℂ] ρ.essentialSpace) ξ) = 0
      change f s = (0 : A) at hs
      rw [hs, map_zero]
      rfl
    have hIntegral : Integrable Ψ μ := hContinuous.integrable_of_hasCompactSupport hSupport
    have hVectorIntegral :
        (∫ s : G, π.algebra (f s) ((π.group s : ρ.essentialSpace →L[ℂ] ρ.essentialSpace) ξ) ∂μ) =
          ((∫ s : G, Ψ s ∂μ : P) : ρ.essentialSpace) := by
      exact P.subtypeL.integral_comp_comm hIntegral
    have hIntegrated := congrArg (fun T : ρ.essentialSpace →L[ℂ] ρ.essentialSpace => T ξ)
      (gramCovariant_haarIntegratedHom μ α p H ρ hp f)
    have hFormula := CovariantRepresentation.haarIntegratedHom_apply_vector μ π f ξ
    have hSource : ρ.essentialRepresentation (p.toNonUnitalCompletion f) ξ =
        ((∫ s : G, Ψ s ∂μ : P) : ρ.essentialSpace) :=
      hIntegrated.symm.trans (hFormula.trans hVectorIntegral)
    rw [hSource]
    exact (∫ s : G, Ψ s ∂μ : P).property
  have hGram : p.rawHilbertGramDomain H ρ ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨f, ξ⟩, rfl⟩
    exact hValues f ξ
  have hDense : (p.rawHilbertGramDomain H ρ).topologicalClosure = ⊤ :=
    Submodule.dense_iff_topologicalClosure_eq_top.mp (p.dense_rawHilbertGramDomain H ρ)
  change P = ⊤
  apply le_antisymm le_top
  rw [← hDense]
  exact (p.rawHilbertGramDomain H ρ).topologicalClosure_minimal hGram S.isClosed_topologicalClosure


/-- **Nondegeneracy of the Gram coefficient representation.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Let p be a C-star
seminorm on the core satisfying p(k)≤∫ s, ‖k(s)‖ ∂μ for every core coefficient k, Xp its
separated completion and ιp its dense map. Let H be a complex Hilbert space and ρ:Xp→B(H) a
nonunital complex star homomorphism. Write E for its essential Hilbert subspace, ρE for the
restricted representation and T(f)=ρE(ιp(f)). The Gram coefficient and group operators P_a,U_g
on E satisfy P_a(T(f)ξ)=T(s↦a*f(s))ξ and U_g(T(f)ξ)=T(s↦α_g(f(g⁻¹*s)))ξ. The complex span of
{P_a ξ:a∈A,ξ∈E} is dense in E, so gramCovariantRepresentation μ α p H ρ hp is nondegenerate.
-/
theorem nondegenerate_gramCovariantRepresentation
    (hp : p ∈ admissibleCStarSeminorms μ α) :
    Dense (Submodule.span ℂ (Set.range fun z : A × ρ.essentialSpace =>
      (gramCovariantRepresentation μ α p H ρ hp).algebra z.1 z.2) : Set ρ.essentialSpace) :=
  (gramCovariantRepresentation μ α p H ρ hp).algebra.essentialSpace_eq_top_iff_dense.mp
    (gramCovariantRepresentation_essentialSpace_eq_top μ α p H ρ hp)

end HilbertModel

/-- **Nondegenerate covariant realization of an admissible seminorm.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Suppose p is a C-star
seminorm on Carrier μ α with p(f)≤∫ s, ‖f(s)‖ ∂μ for every core coefficient f. For G:Type uG
and A:Type uA there exist a complex Hilbert space K:Type(max uG uA) and a covariant
representation π of α on K with ‖Iπ(f)‖=p(f) for every f, where Iπ(f)ξ=∫ s,
π.algebra(f(s))(π.group(s)ξ) ∂μ. Its coefficient essential space is all of K.
-/
theorem exists_admissibleCovariantNormModel_essentialSpace_eq_top (hp : p ∈ admissibleCStarSeminorms μ α) :
    ∃ (K : Type (max uG uA)) (_hK1 : NormedAddCommGroup K)
      (_hK2 : InnerProductSpace ℂ K) (_hK3 : CompleteSpace K)
      (π : CovariantRepresentation α K),
      (∀ f : Carrier μ α, ‖CovariantRepresentation.haarIntegratedHom μ π f‖ = p f) ∧
        π.algebra.essentialSpace = ⊤ := by
  obtain ⟨H₀, hH1, hH2, hH3, ρ₀, hρ₀, _hNorm, _hSource, _hDense⟩ :=
    p.exists_nonUnitalCompletionHilbertNormModel
  let _ : NormedAddCommGroup H₀ := hH1
  let _ : InnerProductSpace ℂ H₀ := hH2
  let _ : CompleteSpace H₀ := hH3
  refine ⟨ρ₀.essentialSpace, inferInstance, inferInstance, inferInstance,
    gramCovariantRepresentation μ α p H₀ ρ₀ hp, ?_, ?_⟩
  · exact norm_gramCovariant_haarIntegratedHom μ α p H₀ ρ₀ hp hρ₀
  · exact gramCovariantRepresentation_essentialSpace_eq_top μ α p H₀ ρ₀ hp


/-- **Covariant seminorm realization with dense coefficient span.**

Let G be a locally compact Borel topological group, μ a regular left Haar measure, A a
nonunital complex C-star algebra and α a point-norm action of G on A. Suppose p is a C-star
seminorm on Carrier μ α with p(f)≤∫ s, ‖f(s)‖ ∂μ for every core coefficient f. For G:Type uG
and A:Type uA there exist a complex Hilbert space K:Type(max uG uA) and a covariant pair (π,U)
on K such that ‖Iπ(f)‖=p(f) for every core coefficient f, where Iπ(f)ξ=∫ s, π(f(s))(U_s ξ) ∂μ
for ξ∈K. The span of π(A)K is dense in K.
-/
theorem exists_admissibleCovariantNormModel (hp : p ∈ admissibleCStarSeminorms μ α) :
    ∃ (K : Type (max uG uA)) (_hK1 : NormedAddCommGroup K)
      (_hK2 : InnerProductSpace ℂ K) (_hK3 : CompleteSpace K)
      (π : CovariantRepresentation α K),
      (∀ f : Carrier μ α, ‖CovariantRepresentation.haarIntegratedHom μ π f‖ = p f) ∧
        Dense (Submodule.span ℂ (Set.range fun z : A × K => π.algebra z.1 z.2) : Set K) := by
  obtain ⟨K, hK1, hK2, hK3, π, hNorm, hNondegenerate⟩ :=
    exists_admissibleCovariantNormModel_essentialSpace_eq_top μ α p hp
  let _ : NormedAddCommGroup K := hK1
  let _ : InnerProductSpace ℂ K := hK2
  let _ : CompleteSpace K := hK3
  exact ⟨K, hK1, hK2, hK3, π, hNorm, π.algebra.essentialSpace_eq_top_iff_dense.mp hNondegenerate⟩

end

end HaarTwistedCore
