/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactScalarFromCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance

/-! Source binding is calibrated on the whole tensor action. The spin and spatial
representatives may each carry a sign, and their product is the relevant scalar.
The actual tensor anchor is an explicit open hypothesis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000

/-- The compact spin paired with the explicit original spatial representative. -/
def generatedTenthAxisLowerRecoverySourceCompactTensor :
    (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ) :=
  coordinateGLTransport conwayTensorCoordinates
    (TensorProduct.congr (generatedTenthAxisLowerRecoverySourceCompactSpin 0).val
      (generatedAxisGlobalFifthShortSpatialWord 2).val)

/-- Quotient equality gives a spatial sign, without choosing an orientation. -/
theorem generatedTenth_axis_lower_recovery_spatial_quotient_scalar
    (a b : leechIsomSubgroup)
    (h : QuotientGroup.mk' signsSubgroup a = QuotientGroup.mk' signsSubgroup b) :
    ∃ d : ℝ, (d = 1 ∨ d = -1) ∧ ∀ x, a.val x = d • b.val x := by
  have hk : a * b⁻¹ ∈ (QuotientGroup.mk' signsSubgroup).ker := by
    change QuotientGroup.mk' signsSubgroup (a * b⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  rw [QuotientGroup.ker_mk'] at hk
  change IsSign (a * b⁻¹) at hk
  rcases hk with hk | hk
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro x
    have hx := congrArg (fun e => e (b.val x)) hk
    change a.val (b.val.symm (b.val x)) = b.val x at hx
    simpa only [LinearEquiv.symm_apply_apply, one_smul] using hx
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro x
    have hx := hk (b.val x)
    change a.val (b.val.symm (b.val x)) = -b.val x at hx
    simpa only [LinearEquiv.symm_apply_apply, neg_one_smul] using hx

/-- The actual chosen spatial component and the explicit source word agree in Co1. -/
theorem generatedTenth_axis_lower_recovery_source_spatial_quotient :
    QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthShortWordFiber 2).val.2 =
      QuotientGroup.mk' signsSubgroup (generatedAxisGlobalFifthShortSpatialWord 2) := by
  change projH (localFiberIntoH (generatedAxisGlobalFifthShortWordFiber 2)) = _
  rw [generatedAxisGlobalFifthShortWordFiber_local]
  exact generatedAxisGlobalFifthShortLocalWord_projection 2

/-- Full tensor factor scalars multiply, including both independent sign choices. -/
theorem generatedTenth_axis_lower_recovery_tensor_factor_scalars
    (a b : SpinSpace ≃ₗ[ℝ] SpinSpace)
    (e f : (Fin 24 → ℝ) ≃ₗ[ℝ] (Fin 24 → ℝ)) (c d : ℝ)
    (ha : ∀ u, a u = c • b u) (he : ∀ v, e v = d • f v)
    (z : SpinSpace ⊗[ℝ] (Fin 24 → ℝ)) :
    TensorProduct.congr a e z = (c * d) • TensorProduct.congr b f z := by
  induction z using TensorProduct.inductionOn with
  | tmul u v =>
    rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul, ha, he,
      TensorProduct.smul_tmul_smul]
  | add u v hu hv =>
    simp only [map_add, hu, hv, smul_add]

private theorem coordinate_tensor_factor_scalars (s : localFiberSubgroup)
    (b : SpinHolomorph) (f : leechIsomSubgroup) (c d : ℝ)
    (hs : ∀ u, s.val.1.val u = c • b.val u)
    (hv : ∀ v, s.val.2.val v = d • f.val v)
    (x : SpinIndex → Fin 24 → ℝ) :
    localTensorRepresentation s x = (c * d) •
      coordinateGLTransport conwayTensorCoordinates (TensorProduct.congr b.val f.val) x := by
  let z := conwayTensorCoordinates.symm x
  have hz := generatedTenth_axis_lower_recovery_tensor_factor_scalars
    s.val.1.val b.val s.val.2.val f.val c d hs hv z
  have ht := congrArg conwayTensorCoordinates hz
  have ha : localTensorAction s = TensorProduct.congr s.val.1.val s.val.2.val := rfl
  simpa only [localTensorRepresentation, MonoidHom.comp_apply, ha,
    coordinateGLTransport_apply, LinearEquiv.map_smul, z] using ht

private theorem coordinate_tensor_sign_exists (s : localFiberSubgroup)
    (b : SpinHolomorph) (f : leechIsomSubgroup)
    (hspin : ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ∀ u, s.val.1.val u = c • b.val u)
    (hspatial : ∃ d : ℝ, (d = 1 ∨ d = -1) ∧ ∀ v, s.val.2.val v = d • f.val v) :
    ∃ k : ℝ, (k = 1 ∨ k = -1) ∧ ∀ x : SpinIndex → Fin 24 → ℝ,
      localTensorRepresentation s x = k •
        coordinateGLTransport conwayTensorCoordinates (TensorProduct.congr b.val f.val) x := by
  obtain ⟨c, hc, hs⟩ := hspin
  obtain ⟨d, hd, hv⟩ := hspatial
  refine ⟨c * d, ?_, ?_⟩
  · rcases hc with hc | hc <;> rcases hd with hd | hd <;>
      simp only [hc, hd, mul_one, mul_neg, neg_neg] <;> tauto
  · intro x
    exact coordinate_tensor_factor_scalars s b f c d hs hv x

@[irreducible] private def sourceTensorFiberOpaque : localFiberSubgroup :=
  generatedAxisGlobalFifthShortWordFiber 2

@[irreducible] private def sourceTensorSpinOpaque : SpinHolomorph :=
  generatedTenthAxisLowerRecoverySourceCompactSpin 0

@[irreducible] private def sourceTensorSpatialOpaque : leechIsomSubgroup :=
  generatedAxisGlobalFifthShortSpatialWord 2

private theorem sourceTensorFiberOpaque_eq :
    sourceTensorFiberOpaque = generatedAxisGlobalFifthShortWordFiber 2 := by
  unfold sourceTensorFiberOpaque
  rfl

private theorem originalSourceSpin_eq :
    generatedTenthAxisLowerRecoveryOriginalSourceSpin =
      (generatedAxisGlobalFifthShortWordFiber 2).val.1 := rfl

private theorem sourceTensorSpinOpaque_eq :
    sourceTensorSpinOpaque = generatedTenthAxisLowerRecoverySourceCompactSpin 0 := by
  unfold sourceTensorSpinOpaque
  rfl

private theorem sourceTensorSpatialOpaque_eq :
    sourceTensorSpatialOpaque = generatedAxisGlobalFifthShortSpatialWord 2 := by
  unfold sourceTensorSpatialOpaque
  rfl

@[irreducible] private def sourceTensorActionOpaque :
    (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ) :=
  localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber 2)

@[irreducible] private def sourceTensorCompactActionOpaque :
    (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ) :=
  generatedTenthAxisLowerRecoverySourceCompactTensor

private theorem sourceTensorActionOpaque_eq :
    sourceTensorActionOpaque =
      localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber 2) := by
  unfold sourceTensorActionOpaque
  rfl

private theorem sourceTensorCompactActionOpaque_eq :
    sourceTensorCompactActionOpaque = generatedTenthAxisLowerRecoverySourceCompactTensor := by
  unfold sourceTensorCompactActionOpaque
  rfl

private theorem coordinate_tensor_sign_exists_named
    (s : localFiberSubgroup) (b : SpinHolomorph) (f : leechIsomSubgroup)
    (a t : (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ))
    (ha : a = localTensorRepresentation s)
    (ht : t = coordinateGLTransport conwayTensorCoordinates
      (TensorProduct.congr b.val f.val))
    (hspin : ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ∀ u, s.val.1.val u = c • b.val u)
    (hspatial : ∃ d : ℝ, (d = 1 ∨ d = -1) ∧ ∀ v, s.val.2.val v = d • f.val v) :
    ∃ k : ℝ, (k = 1 ∨ k = -1) ∧ ∀ x : SpinIndex → Fin 24 → ℝ, a x = k • t x := by
  rw [ha, ht]
  exact coordinate_tensor_sign_exists s b f hspin hspatial

private theorem scalar_sign_transport {A V : Type*} [SMul ℝ V]
    (act : A → V → V) (a₁ a₂ b₁ b₂ : A) (ha : a₁ = a₂) (hb : b₁ = b₂)
    (h : ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ∀ x, act a₂ x = c • act b₂ x) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ ∀ x, act a₁ x = c • act b₁ x := by
  cases ha
  cases hb
  exact h

set_option maxHeartbeats 200000 in
-- Bound the concrete original-word comparison after the generic scalar argument.
/-- The genuine source tensor and compact tensor differ by one combined scalar. -/
theorem generatedTenth_axis_lower_recovery_source_tensor_scalar :
    ∃ k : ℝ, (k = 1 ∨ k = -1) ∧ ∀ x : SpinIndex → Fin 24 → ℝ,
      localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber 2) x =
        k • generatedTenthAxisLowerRecoverySourceCompactTensor x := by
  have hspin := generatedTenth_axis_lower_recovery_source_compact_scalar
  have hspinOpaque := scalar_sign_transport
    (fun (s : SpinHolomorph) (u : SpinSpace) => s.val u)
    sourceTensorFiberOpaque.val.1 generatedTenthAxisLowerRecoveryOriginalSourceSpin
    sourceTensorSpinOpaque (generatedTenthAxisLowerRecoverySourceCompactSpin 0)
    ((congrArg (fun s : localFiberSubgroup => s.val.1) sourceTensorFiberOpaque_eq).trans
      originalSourceSpin_eq.symm)
    sourceTensorSpinOpaque_eq hspin
  have hspatial := generatedTenth_axis_lower_recovery_spatial_quotient_scalar
    (generatedAxisGlobalFifthShortWordFiber 2).val.2
    (generatedAxisGlobalFifthShortSpatialWord 2)
    generatedTenth_axis_lower_recovery_source_spatial_quotient
  have hspatialOpaque := scalar_sign_transport
    (fun (s : leechIsomSubgroup) (u : Fin 24 → ℝ) => s.val u)
    sourceTensorFiberOpaque.val.2 (generatedAxisGlobalFifthShortWordFiber 2).val.2
    sourceTensorSpatialOpaque (generatedAxisGlobalFifthShortSpatialWord 2)
    (congrArg (fun s : localFiberSubgroup => s.val.2) sourceTensorFiberOpaque_eq)
    sourceTensorSpatialOpaque_eq hspatial
  have ha : sourceTensorActionOpaque = localTensorRepresentation sourceTensorFiberOpaque :=
    sourceTensorActionOpaque_eq.trans
      (congrArg (fun s : localFiberSubgroup => localTensorRepresentation s)
        sourceTensorFiberOpaque_eq).symm
  have hc : generatedTenthAxisLowerRecoverySourceCompactTensor =
      coordinateGLTransport conwayTensorCoordinates
        (TensorProduct.congr (generatedTenthAxisLowerRecoverySourceCompactSpin 0).val
          (generatedAxisGlobalFifthShortSpatialWord 2).val) := rfl
  have ht : sourceTensorCompactActionOpaque =
      coordinateGLTransport conwayTensorCoordinates
        (TensorProduct.congr sourceTensorSpinOpaque.val sourceTensorSpatialOpaque.val) :=
    sourceTensorCompactActionOpaque_eq.trans (hc.trans
      (congrArg₂ (fun (b : SpinHolomorph) (f : leechIsomSubgroup) =>
        coordinateGLTransport conwayTensorCoordinates (TensorProduct.congr b.val f.val))
        sourceTensorSpinOpaque_eq sourceTensorSpatialOpaque_eq).symm)
  have hOpaque := coordinate_tensor_sign_exists_named
    sourceTensorFiberOpaque sourceTensorSpinOpaque sourceTensorSpatialOpaque
    sourceTensorActionOpaque sourceTensorCompactActionOpaque ha ht hspinOpaque hspatialOpaque
  exact scalar_sign_transport
    (fun (a : (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ))
      (x : SpinIndex → Fin 24 → ℝ) => a x)
    (localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber 2))
    sourceTensorActionOpaque generatedTenthAxisLowerRecoverySourceCompactTensor
    sourceTensorCompactActionOpaque sourceTensorActionOpaque_eq.symm
    sourceTensorCompactActionOpaque_eq.symm hOpaque

/-- The initial delta tensor vector in physical coordinates. -/
def generatedTenthAxisLowerRecoverySourceTensorAnchorInput : SpinIndex → Fin 24 → ℝ :=
  fun t i => ((Pi.single (0 : SpinIndex) (1 : ℝ)) : SpinIndex → ℝ) t *
    ((Pi.single (0 : Fin 24) ((Real.sqrt 2)⁻¹)) : Fin 24 → ℝ) i

/-- Two complete coordinate actions have the same prescribed anchor value. -/
@[irreducible] def generatedTenthAxisLowerRecoveryTensorAnchorPredicate
    (a b : (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ))
    (v : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) (r : ℝ) : Prop :=
  a v t i = r ∧ b v t i = r

private theorem tensor_anchor_predicate_iff
    (a b : (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ))
    (v : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) (r : ℝ) :
    generatedTenthAxisLowerRecoveryTensorAnchorPredicate a b v t i r ↔
      (a v t i = r ∧ b v t i = r) := by
  unfold generatedTenthAxisLowerRecoveryTensorAnchorPredicate
  exact Iff.rfl

/-- Both genuinely evaluated tensor coordinates must have the retained nonzero value.
The separated numerical spin value alone does not establish this condition. -/
def generatedTenthAxisLowerRecoverySourceTensorAnchorCondition : Prop :=
  generatedTenthAxisLowerRecoveryTensorAnchorPredicate
    (localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber 2))
    generatedTenthAxisLowerRecoverySourceCompactTensor
    generatedTenthAxisLowerRecoverySourceTensorAnchorInput (golayLabelCoefficients 0) 0
    (-1 / (256 * Real.sqrt 2))

/-- The two original coordinate equalities establish the unchanged complete anchor condition. -/
theorem generatedTenth_source_tensor_anchor_of_coordinates
    (ha : localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber 2)
      generatedTenthAxisLowerRecoverySourceTensorAnchorInput
      (golayLabelCoefficients 0) 0 = -1 / (256 * Real.sqrt 2))
    (hb : generatedTenthAxisLowerRecoverySourceCompactTensor
      generatedTenthAxisLowerRecoverySourceTensorAnchorInput
      (golayLabelCoefficients 0) 0 = -1 / (256 * Real.sqrt 2)) :
    generatedTenthAxisLowerRecoverySourceTensorAnchorCondition :=
  (tensor_anchor_predicate_iff
    (localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber 2))
    generatedTenthAxisLowerRecoverySourceCompactTensor
    generatedTenthAxisLowerRecoverySourceTensorAnchorInput (golayLabelCoefficients 0) 0
    (-1 / (256 * Real.sqrt 2))).mpr ⟨ha, hb⟩

private theorem tensor_scalar_eq_of_anchor
    (a b : (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ))
    (k : ℝ) (hk : k = 1 ∨ k = -1) (hs : ∀ x, a x = k • b x)
    (v : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) (r : ℝ)
    (hr : r ≠ 0) (ha : a v t i = r) (hb : b v t i = r) : a = b := by
  have hk1 : k = 1 := by
    rcases hk with hk | hk
    · exact hk
    · exfalso
      have h := congrFun (congrFun (hs v) t) i
      simp only [Pi.smul_apply, smul_eq_mul, hk, neg_one_mul] at h
      rw [ha, hb] at h
      apply hr
      linarith
  apply LinearEquiv.ext
  intro x
  simpa only [hk1, one_smul] using hs x

private theorem tensor_scalar_eq_of_named_anchor
    (a b : (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ))
    (v : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) (r : ℝ)
    (p : Prop) (hp : p ↔ (a v t i = r ∧ b v t i = r))
    (hsign : ∃ k : ℝ, (k = 1 ∨ k = -1) ∧ ∀ x, a x = k • b x)
    (hr : r ≠ 0) (h : p) : a = b := by
  obtain ⟨k, hk, hs⟩ := hsign
  obtain ⟨ha, hb⟩ := hp.mp h
  exact tensor_scalar_eq_of_anchor a b k hk hs v t i r hr ha hb

private theorem anchor_predicate_transport
    (a₁ a₂ b₁ b₂ : (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ))
    (ha : a₁ = a₂) (hb : b₁ = b₂)
    (v : SpinIndex → Fin 24 → ℝ) (t : SpinIndex) (i : Fin 24) (r : ℝ) (p : Prop)
    (hp : p ↔ (a₂ v t i = r ∧ b₂ v t i = r)) :
    p ↔ (a₁ v t i = r ∧ b₁ v t i = r) := by
  cases ha
  cases hb
  exact hp

private theorem source_tensor_anchor_nonzero :
    (-1 : ℝ) / (256 * Real.sqrt 2) ≠ 0 := by
  apply div_ne_zero (by norm_num)
  exact mul_ne_zero (by norm_num) (Real.sqrt_ne_zero'.mpr (by norm_num))

set_option maxHeartbeats 200000 in
-- Bound elaboration of the original source action against its complete tensor anchor.
/-- One genuine nonzero combined tensor coordinate closes the whole source binding. -/
theorem generatedTenth_axis_lower_recovery_source_tensor_actual
    (hanchor : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition) :
    localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber 2) =
      generatedTenthAxisLowerRecoverySourceCompactTensor := by
  have hsign := generatedTenth_axis_lower_recovery_source_tensor_scalar
  have hsignOpaque := scalar_sign_transport
    (fun (a : (SpinIndex → Fin 24 → ℝ) ≃ₗ[ℝ] (SpinIndex → Fin 24 → ℝ))
      (x : SpinIndex → Fin 24 → ℝ) => a x)
    sourceTensorActionOpaque (localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber 2))
    sourceTensorCompactActionOpaque generatedTenthAxisLowerRecoverySourceCompactTensor
    sourceTensorActionOpaque_eq sourceTensorCompactActionOpaque_eq hsign
  have hn := source_tensor_anchor_nonzero
  have hpActual : generatedTenthAxisLowerRecoverySourceTensorAnchorCondition ↔
      (localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber 2)
          generatedTenthAxisLowerRecoverySourceTensorAnchorInput (golayLabelCoefficients 0) 0 =
        -1 / (256 * Real.sqrt 2) ∧
      generatedTenthAxisLowerRecoverySourceCompactTensor
          generatedTenthAxisLowerRecoverySourceTensorAnchorInput (golayLabelCoefficients 0) 0 =
        -1 / (256 * Real.sqrt 2)) :=
    tensor_anchor_predicate_iff
      (localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber 2))
      generatedTenthAxisLowerRecoverySourceCompactTensor
      generatedTenthAxisLowerRecoverySourceTensorAnchorInput (golayLabelCoefficients 0) 0
      (-1 / (256 * Real.sqrt 2))
  have hpOpaque := anchor_predicate_transport
    sourceTensorActionOpaque (localTensorRepresentation (generatedAxisGlobalFifthShortWordFiber 2))
    sourceTensorCompactActionOpaque generatedTenthAxisLowerRecoverySourceCompactTensor
    sourceTensorActionOpaque_eq sourceTensorCompactActionOpaque_eq
    generatedTenthAxisLowerRecoverySourceTensorAnchorInput (golayLabelCoefficients 0) 0
    (-1 / (256 * Real.sqrt 2)) generatedTenthAxisLowerRecoverySourceTensorAnchorCondition hpActual
  have hclosed := tensor_scalar_eq_of_named_anchor
    sourceTensorActionOpaque sourceTensorCompactActionOpaque
    generatedTenthAxisLowerRecoverySourceTensorAnchorInput (golayLabelCoefficients 0) 0
    (-1 / (256 * Real.sqrt 2)) generatedTenthAxisLowerRecoverySourceTensorAnchorCondition
    hpOpaque hsignOpaque hn hanchor
  exact sourceTensorActionOpaque_eq.symm.trans (hclosed.trans sourceTensorCompactActionOpaque_eq)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
