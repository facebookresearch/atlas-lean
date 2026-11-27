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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.VectorFunctionalCriterion
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.RegularCoefficientAlgebra
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalAction.SpatialCoefficient
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Normality of Haar regular coefficient representations

For a normal action `α` and regular Haar measure `μ`, every vector functional pulled back
through the regular coefficient map `x ↦ P_x` belongs to `M_*`. For compact-support vectors it
is represented by the corresponding predual integral; norm density extends the result to all L²
vectors.

Thus `M → B(Lp H 2 μ)` is a normal star homomorphism. The unitarily transported tensor
coefficient map is also normal into `M ⊗̄ B(Lp ℂ 2 μ)`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open MathlibExt.Analysis.CStarAlgebra
open scoped ENNReal Topology CompactlySupported TensorProduct InnerProductSpace CStarAlgebra

namespace VonNeumannAlgebra.NormalAction

noncomputable section

universe uG uH

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (μ : Measure G) [μ.Regular]

/-- **Normal pullback of a compact-support Haar vector coefficient.** Let `G` be a group with
a topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra,
and `α` a normal action with norm-continuous inverse predual orbits. Assume `G` is a
topological group. Assume `G` is locally compact with its Borel measurable structure, and
`μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar
invariance is not assumed. Assume additionally that `μ` is a Haar measure. for
`f,g∈C_c(G,H)` with L² inclusion `i_μ`, the bounded functional `x ↦ ⟨i_μ f,P_x(i_μ g)⟩`
belongs to `M_*`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficient_compactVectorFunctional_mem_normalFunctionalSpace [μ.IsHaarMeasure]
    (α : NormalAction G M) (f g : C_c(G, H)) :
    representationCoefficient (regularCoefficientHom μ α)
      (MeasureTheory.HaarL2.compactSupportInclusion μ g)
      (MeasureTheory.HaarL2.compactSupportInclusion μ f) ∈ normalFunctionalSpace M := by
  let j₀ : M →ₗ[ℂ] (H →L[ℂ] H) := LinearMap.ofClass M.toStarSubalgebra.subtype
  let j : M →L[ℂ] (H →L[ℂ] H) := j₀.mkContinuous 1 (by
    intro x
    change ‖(x : H →L[ℂ] H)‖ ≤ 1 * ‖x‖
    rw [one_mul]
    exact le_rfl)
  let Ev : H →L[ℂ] (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H
  let J : H →L[ℂ] M →L[ℂ] H := (Ev.flip.comp j).flip
  let V : H →L⋆[ℂ] H →L[ℂ] StrongDual ℂ M :=
    ContinuousLinearMap.bilinearComp (ContinuousLinearMap.compL ℂ M H ℂ) (innerSL ℂ) J
  have hj (x : M) : j x = (x : H →L[ℂ] H) := by
    dsimp only [j]
    rw [LinearMap.mkContinuous_apply]
    rfl
  have hEv (a : H) (T : H →L[ℂ] H) : Ev a T = T a :=
    ContinuousLinearMap.apply_apply a T
  have hJ (a : H) (x : M) : J a x = (j x) a := by
    dsimp only [J]
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    exact hEv a (j x)
  have hEval (a b : H) (x : M) : V a b x = inner ℂ a ((x : H →L[ℂ] H) b) := by
    calc
      V a b x = innerSL ℂ a (J b x) := by
        simp only [V, ContinuousLinearMap.bilinearComp_apply,
          ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
      _ = inner ℂ a ((j x) b) := by rw [hJ, innerSL_apply_apply]
      _ = inner ℂ a ((x : H →L[ℂ] H) b) := by rw [hj]
  have hV (a b : H) : V a b = vectorFunctional M a b := by
    apply ContinuousLinearMap.ext
    intro x
    exact (hEval a b x).trans (vectorFunctional_apply M a b x).symm
  have hpredual (s : G) (φ : normalFunctionalSpace M) : ‖α.predualAction s φ‖ ≤ ‖φ‖ := by
    change ‖(α.predualAction s φ : StrongDual ℂ M)‖ ≤ ‖φ‖
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ)
    intro x
    rw [predualAction_apply]
    calc
      ‖(φ : StrongDual ℂ M) ((α s).symm x)‖ ≤ ‖φ‖ * ‖(α s).symm x‖ :=
        (φ : StrongDual ℂ M).le_opNorm ((α s).symm x)
      _ ≤ ‖φ‖ * ‖x‖ := mul_le_mul_of_nonneg_left
        (NonUnitalStarAlgHom.norm_apply_le (α s).symm.toNormalStarAlgHom.toStarAlgHom x)
        (norm_nonneg φ)
  let φ (s : G) : normalFunctionalSpace M :=
    ⟨V (f s) (g s), by rw [hV]; exact vectorFunctional_mem_normalFunctionalSpace M (f s) (g s)⟩
  let F (s : G) : normalFunctionalSpace M := α.predualAction s (φ s)
  have hφ : Continuous φ := by
    exact Continuous.subtype_mk
      ((V.continuous.comp (map_continuous f)).clm_apply (map_continuous g)) _
  have hF : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro s₀
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hfirst : Tendsto (fun s => ‖φ s - φ s₀‖) (𝓝 s₀) (𝓝 0) := by
      have hc : Continuous (fun s : G => ‖φ s - φ s₀‖) := by
        simpa only [Pi.sub_apply] using
          (hφ.sub (continuous_const : Continuous (fun _ : G => φ s₀))).norm
      simpa only [sub_self, norm_zero] using hc.tendsto s₀
    have hsecond : Tendsto (fun s => ‖α.predualAction s (φ s₀) - α.predualAction s₀ (φ s₀)‖)
        (𝓝 s₀) (𝓝 0) := by
      have hc : Continuous (fun s : G => ‖α.predualAction s (φ s₀) - α.predualAction s₀ (φ s₀)‖) := by
        simpa only [Pi.sub_apply] using
          ((α.predualAction_continuous (φ s₀)).sub
            (continuous_const : Continuous (fun _ : G => α.predualAction s₀ (φ s₀)))).norm
      simpa only [sub_self, norm_zero] using hc.tendsto s₀
    have hbound (s : G) : ‖F s - F s₀‖ ≤
        ‖φ s - φ s₀‖ + ‖α.predualAction s (φ s₀) - α.predualAction s₀ (φ s₀)‖ := by
      calc
        ‖F s - F s₀‖ =
            ‖α.predualAction s (φ s - φ s₀) +
              (α.predualAction s (φ s₀) - α.predualAction s₀ (φ s₀))‖ := by
          rw [map_sub, sub_add_sub_cancel]
        _ ≤ ‖α.predualAction s (φ s - φ s₀)‖ +
            ‖α.predualAction s (φ s₀) - α.predualAction s₀ (φ s₀)‖ := norm_add_le _ _
        _ ≤ ‖φ s - φ s₀‖ + ‖α.predualAction s (φ s₀) - α.predualAction s₀ (φ s₀)‖ :=
          add_le_add (hpredual s (φ s - φ s₀)) le_rfl
    exact squeeze_zero (fun s => norm_nonneg (F s - F s₀)) hbound
      (by simpa only [zero_add] using hfirst.add hsecond)
  have hFc : HasCompactSupport F := by
    refine HasCompactSupport.intro f.hasCompactSupport ?_
    intro s hs
    have hf : f s = 0 := image_eq_zero_of_notMem_tsupport hs
    have hφzero : φ s = 0 := by
      apply Subtype.ext
      apply ContinuousLinearMap.ext
      intro x
      change V (f s) (g s) x = 0
      rw [hV, vectorFunctional_apply, hf, inner_zero_left]
    change α.predualAction s (φ s) = 0
    rw [hφzero, map_zero]
  let _ : NormedSpace ℝ (normalFunctionalSpace M) :=
    NormedSpace.restrictScalars ℝ ℂ (normalFunctionalSpace M)
  have hFLp : MemLp F 1 μ := hF.memLp_of_hasCompactSupport hFc
  have hFI : Integrable F μ := memLp_one_iff_integrable.mp hFLp
  let I : normalFunctionalSpace M := ∫ s, F s ∂μ
  have hI (x : M) : (I : StrongDual ℂ M) x =
      ∫ s, inner ℂ (f s) ((α s⁻¹ x : H →L[ℂ] H) (g s)) ∂μ := by
    change normalFunctionalEvaluation M x I = _
    rw [← (normalFunctionalEvaluation M x).integral_comp_comm hFI]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun s => by
      change normalFunctionalEvaluation M x (F s) =
        inner ℂ (f s) ((α s⁻¹ x : H →L[ℂ] H) (g s))
      calc
        normalFunctionalEvaluation M x (F s) = (F s : StrongDual ℂ M) x :=
          normalFunctionalEvaluation_apply M x (F s)
        _ = (φ s : StrongDual ℂ M) ((α s).symm x) := predualAction_apply α s (φ s) x
        _ = V (f s) (g s) ((α s).symm x) := rfl
        _ = inner ℂ (f s) (((α s).symm x : H →L[ℂ] H) (g s)) := hEval (f s) (g s) ((α s).symm x)
        _ = inner ℂ (f s) ((α s⁻¹ x : H →L[ℂ] H) (g s)) := by rw [map_inv]; rfl
  let r := regularCoefficientHom μ α
  have hrep (x : M) :
      representationCoefficient r (MeasureTheory.HaarL2.compactSupportInclusion μ g)
          (MeasureTheory.HaarL2.compactSupportInclusion μ f) x =
        ∫ s, inner ℂ (f s) ((α s⁻¹ x : H →L[ℂ] H) (g s)) ∂μ := by
    calc
      representationCoefficient r (MeasureTheory.HaarL2.compactSupportInclusion μ g)
          (MeasureTheory.HaarL2.compactSupportInclusion μ f) x =
          inner ℂ (MeasureTheory.HaarL2.compactSupportInclusion μ f)
            (r x (MeasureTheory.HaarL2.compactSupportInclusion μ g)) :=
        representationCoefficient_apply r (MeasureTheory.HaarL2.compactSupportInclusion μ g)
          (MeasureTheory.HaarL2.compactSupportInclusion μ f) x
      _ = ∫ s, inner ℂ (MeasureTheory.HaarL2.compactSupportInclusion μ f s)
          (regularCoefficient μ α x (MeasureTheory.HaarL2.compactSupportInclusion μ g) s) ∂μ := by
        exact L2.inner_def (MeasureTheory.HaarL2.compactSupportInclusion μ f)
          (regularCoefficient μ α x (MeasureTheory.HaarL2.compactSupportInclusion μ g))
      _ = ∫ s, inner ℂ (f s) ((α s⁻¹ x : H →L[ℂ] H) (g s)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [MeasureTheory.HaarL2.compactSupportInclusion_ae_eq μ f,
          regularCoefficient_ae_eq μ α x (MeasureTheory.HaarL2.compactSupportInclusion μ g),
          MeasureTheory.HaarL2.compactSupportInclusion_ae_eq μ g] with s hf hx hg
        rw [hf, hx, hg]
  have hEq : (I : StrongDual ℂ M) =
      representationCoefficient r (MeasureTheory.HaarL2.compactSupportInclusion μ g)
        (MeasureTheory.HaarL2.compactSupportInclusion μ f) := by
    apply ContinuousLinearMap.ext
    intro x
    exact (hI x).trans (hrep x).symm
  rw [← hEq]
  exact I.property

/-- **Normal pullback of every Haar L² vector coefficient.** Let `G` be a group with a
topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann algebra,
and `α` a normal action with norm-continuous inverse predual orbits. Assume `G` is a
topological group. Assume `G` is locally compact with its Borel measurable structure, and
`μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`. Haar
invariance is not assumed. Assume additionally that `μ` is a Haar measure. for `ξ,η∈L`,
the functional `x ↦ ⟨ξ,P_xη⟩` belongs to the normal-functional space `M_*`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
theorem regularCoefficient_vectorFunctional_mem_normalFunctionalSpace [μ.IsHaarMeasure]
    (α : NormalAction G M) (ξ η : Lp H 2 μ) :
    representationCoefficient (regularCoefficientHom μ α) η ξ ∈ normalFunctionalSpace M := by
  let r := regularCoefficientHom μ α
  let jr : M →L[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) := ⟨r.toLinearMap, map_continuous r⟩
  let Evr : Lp H 2 μ →L[ℂ] (Lp H 2 μ →L[ℂ] Lp H 2 μ) →L[ℂ] Lp H 2 μ :=
    ContinuousLinearMap.apply ℂ (Lp H 2 μ)
  let Jr : Lp H 2 μ →L[ℂ] M →L[ℂ] Lp H 2 μ := (Evr.flip.comp jr).flip
  let Vr : Lp H 2 μ →L⋆[ℂ] Lp H 2 μ →L[ℂ] StrongDual ℂ M :=
    ContinuousLinearMap.bilinearComp (ContinuousLinearMap.compL ℂ M (Lp H 2 μ) ℂ) (innerSL ℂ) Jr
  have hjr (x : M) : jr x = r x := rfl
  have hEvr (a : Lp H 2 μ) (T : Lp H 2 μ →L[ℂ] Lp H 2 μ) : Evr a T = T a :=
    ContinuousLinearMap.apply_apply a T
  have hJr (a : Lp H 2 μ) (x : M) : Jr a x = (jr x) a := by
    dsimp only [Jr]
    rw [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    exact hEvr a (jr x)
  have hEvalr (a b : Lp H 2 μ) (x : M) : Vr a b x = inner ℂ a ((r x) b) := by
    calc
      Vr a b x = innerSL ℂ a (Jr b x) := by
        simp only [Vr, ContinuousLinearMap.bilinearComp_apply,
          ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
      _ = inner ℂ a ((jr x) b) := by rw [hJr, innerSL_apply_apply]
      _ = inner ℂ a ((r x) b) := by rw [hjr]
  have hVr (a b : Lp H 2 μ) : Vr a b = representationCoefficient r b a := by
    apply ContinuousLinearMap.ext
    intro x
    exact (hEvalr a b x).trans (representationCoefficient_apply r b a x).symm
  have hcompact (f g : C_c(G, H)) :
      Vr (MeasureTheory.HaarL2.compactSupportInclusion μ f)
        (MeasureTheory.HaarL2.compactSupportInclusion μ g) ∈ normalFunctionalSpace M := by
    rw [hVr]
    exact regularCoefficient_compactVectorFunctional_mem_normalFunctionalSpace μ α f g
  have hall (a b : Lp H 2 μ) : Vr a b ∈ normalFunctionalSpace M := by
    refine (MeasureTheory.HaarL2.denseRange_compactSupportInclusion (H := H) μ).induction_on a
      ((normalFunctionalSpace_isClosed M).preimage (Vr.flip b).continuous) ?_
    intro f
    refine (MeasureTheory.HaarL2.denseRange_compactSupportInclusion (H := H) μ).induction_on b
      ((normalFunctionalSpace_isClosed M).preimage
        (Vr (MeasureTheory.HaarL2.compactSupportInclusion μ f)).continuous) ?_
    intro g
    exact hcompact f g
  rw [← hVr]
  exact hall ξ η

/-- **Normal homomorphism of the Haar regular coefficient representation.** Let `G` be a group
with a topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann
algebra, and `α` a normal action with norm-continuous inverse predual orbits. Assume `G`
is a topological group. Assume `G` is locally compact with its Borel measurable structure,
and `μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`.
Haar invariance is not assumed. Assume additionally that `μ` is a Haar measure.
`regularCoefficientNormalHom μ α : NormalStarAlgHom M B(L)` is the ultraweakly continuous
unital star map `x ↦ P_x`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
def regularCoefficientNormalHom [μ.IsHaarMeasure] (α : NormalAction G M) :
    NormalStarAlgHom M (⊤ : VonNeumannAlgebra (Lp H 2 μ)) := by
  let r := regularCoefficientHom μ α
  let f : M →⋆ₐ[ℂ] (⊤ : VonNeumannAlgebra (Lp H 2 μ)) :=
    { toFun x := ⟨r x, by
        change r x ∈ (⊤ : StarSubalgebra ℂ (Lp H 2 μ →L[ℂ] Lp H 2 μ))
        trivial⟩
      map_one' := by apply Subtype.ext; exact map_one r
      map_mul' x y := by apply Subtype.ext; exact map_mul r x y
      map_zero' := by apply Subtype.ext; exact map_zero r
      map_add' x y := by apply Subtype.ext; exact map_add r x y
      commutes' c := by apply Subtype.ext; exact r.commutes c
      map_star' x := by apply Subtype.ext; exact map_star r x }
  refine NormalStarAlgHom.ofVectorFunctionalPullbacks f ?_
  intro ξ η
  have hEq : (vectorFunctional (⊤ : VonNeumannAlgebra (Lp H 2 μ)) ξ η).comp
      (⟨LinearMap.ofClass f, map_continuous f⟩ : M →L[ℂ] (⊤ : VonNeumannAlgebra (Lp H 2 μ))) =
      representationCoefficient r η ξ := by
    apply ContinuousLinearMap.ext
    intro x
    rw [ContinuousLinearMap.comp_apply, vectorFunctional_apply, representationCoefficient_apply]
    rfl
  rw [hEq]
  exact regularCoefficient_vectorFunctional_mem_normalFunctionalSpace μ α ξ η

/-- **Normal tensor coefficient map into the full-right spatial algebra.** Let `G` be a group
with a topology, `H` a complete complex Hilbert space, `M⊆B(H)` a concrete von Neumann
algebra, and `α` a normal action with norm-continuous inverse predual orbits. Assume `G`
is a topological group. Assume `G` is locally compact with its Borel measurable structure,
and `μ` is a regular measure. On `L=Lp H 2 μ`, put `P_x ξ =ᵐ[μ] (s ↦ α_(s⁻¹)(x)ξ(s))`.
Haar invariance is not assumed. Let `T=Completion(H ⊗[ℂ] Lp ℂ 2 μ)` and `U : T ≃ₗᵢ[ℂ] L`
be `tensorToLpRight μ`, with `U(ξ⊗f) =ᵐ[μ] (s ↦ f(s) • ξ)`. Set `Q_x=U⁻¹ P_x U`. Assume
additionally that `μ` is a Haar measure. `regularCoefficientSpatialNormalHom μ α :
NormalStarAlgHom M (M ⊗̄ B(Lp ℂ 2 μ))` has operator value `x ↦ Q_x`.

Here `=ᵐ[μ]` denotes equality of measurable representatives μ-almost everywhere, not point
evaluation of an L² class. Operator identities are equalities of bounded operators. -/
def regularCoefficientSpatialNormalHom [μ.IsHaarMeasure] (α : NormalAction G M) :
    NormalStarAlgHom M (spatialTensorProduct M (⊤ : VonNeumannAlgebra (Lp ℂ 2 μ))) := by
  let E := L2.tensorToLpRight (𝕜 := ℂ) (H := H) μ
  let f := regularCoefficientSpatialHom μ α
  let r := regularCoefficientHom μ α
  let t := regularCoefficientTensorHom μ α
  have hE (x : M) (z : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) :
      E (t x z) = r x (E z) := by
    change E (E.symm (regularCoefficient μ α x (E z))) = _
    exact E.apply_symm_apply _
  have hfvalue (x : M) :
      (f x : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
        UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) = t x := by
    change regularCoefficientTensor μ α x = regularCoefficientTensorHom μ α x
    exact (regularCoefficientTensorHom_apply μ α x).symm
  refine NormalStarAlgHom.ofVectorFunctionalPullbacks f ?_
  intro ξ η
  have hEq : (vectorFunctional
        (spatialTensorProduct M (⊤ : VonNeumannAlgebra (Lp ℂ 2 μ))) ξ η).comp
      (⟨LinearMap.ofClass f, map_continuous f⟩ :
        M →L[ℂ] spatialTensorProduct M (⊤ : VonNeumannAlgebra (Lp ℂ 2 μ))) =
      representationCoefficient t η ξ := by
    apply ContinuousLinearMap.ext
    intro x
    calc
      _ = vectorFunctional
          (spatialTensorProduct M (⊤ : VonNeumannAlgebra (Lp ℂ 2 μ))) ξ η (f x) := rfl
      _ = inner ℂ ξ ((f x : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ))) η) :=
        vectorFunctional_apply (spatialTensorProduct M (⊤ : VonNeumannAlgebra (Lp ℂ 2 μ))) ξ η (f x)
      _ = inner ℂ ξ ((t x) η) :=
        congrArg (fun C : UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) →L[ℂ]
          UniformSpace.Completion (H ⊗[ℂ] (Lp ℂ 2 μ)) => inner ℂ ξ (C η)) (hfvalue x)
      _ = representationCoefficient t η ξ x := (representationCoefficient_apply t η ξ x).symm
  have htransport := representationCoefficient_unitaryIntertwiner t r E hE η ξ
  rw [hEq, ← htransport]
  exact regularCoefficient_vectorFunctional_mem_normalFunctionalSpace μ α (E ξ) (E η)

end

end VonNeumannAlgebra.NormalAction
