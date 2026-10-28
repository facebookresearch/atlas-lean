/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.SpinOrthogonalLift
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.BinaryAutomorphism
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechQuadratic

/-! Exactness and faithfulness for the concrete local group.

The inclusion of the extraspecial group is injective, and the concrete local
Griess action is faithful. The projection is surjective and its kernel is
exactly the image of Q, proving the concrete local exact sequence. -/

@[expose] public section
open scoped Pointwise TensorProduct
open Multiplicative
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

theorem localFiberIncl_diagonal_iff (g : Q) :
    localFiberIncl g ∈ localDiagonalSubgroup ↔ g = 1 := by
  constructor
  · rintro ⟨c, hc, he⟩
    have hv := congrFun (he (fun _ => 1)) (0 : Fin 24)
    change (1 : ℝ) = qSign c * 1 at hv
    have hs : qSign c = 1 := by simpa using hv.symm
    have hzero := (qSign_eq_one_iff c).mp hs
    apply spinRepresentation_injective
    apply LinearEquiv.ext
    intro u
    rw [map_one]
    change spinRepresentation g u = u
    have hu := hc u
    change spinRepresentation g u = qSign c • u at hu
    simpa [hzero] using hu
  · rintro rfl
    rw [map_one]
    exact localDiagonalSubgroup.one_mem

theorem inclQ_injective : Function.Injective inclQ := by
  apply (MonoidHom.ker_eq_bot_iff inclQ).mp
  ext g
  change inclQ g = 1 ↔ g = 1
  change QuotientGroup.mk' localDiagonalSubgroup (localFiberIncl g) = 1 ↔ g = 1
  change QuotientGroup.mk (localFiberIncl g) =
    (1 : localFiberSubgroup ⧸ localDiagonalSubgroup) ↔ g = 1
  rw [QuotientGroup.eq_one_iff]
  exact localFiberIncl_diagonal_iff g

theorem projH_inclQ (g : Q) : projH (inclQ g) = 1 := by
  change localFiberProjection (localFiberIncl g) = 1
  change QuotientGroup.mk' signsSubgroup 1 = 1
  exact map_one _

theorem inclQ_range_le_projH_ker : inclQ.range ≤ projH.ker := by
  rintro h ⟨g, rfl⟩
  exact projH_inclQ g
theorem conwayTensorCoordinates_tmul (u : SpinSpace) (v : Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) :
    conwayTensorCoordinates (u ⊗ₜ[ℝ] v) t i = u t * v i := by
  change TensorProduct.piScalarRight ℝ ℝ SpinSpace (Fin 24) (u ⊗ₜ[ℝ] v) i t = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  change v i * u t = u t * v i
  exact mul_comm _ _

theorem localTensorAction_trivial_pairing (f : localFiberSubgroup)
    (hf : localTensorAction f = 1) (u : SpinSpace) (v : Fin 24 → ℝ)
    (t : SpinIndex) (i : Fin 24) :
    f.val.1.val u t * f.val.2.val v i = u t * v i := by
  have h := congrArg (fun e => conwayTensorCoordinates (e (u ⊗ₜ[ℝ] v)) t i) hf
  change conwayTensorCoordinates
    (TensorProduct.congr f.val.1.val f.val.2.val (u ⊗ₜ[ℝ] v)) t i =
    conwayTensorCoordinates (u ⊗ₜ[ℝ] v) t i at h
  rw [TensorProduct.congr_tmul, conwayTensorCoordinates_tmul,
    conwayTensorCoordinates_tmul] at h
  exact h

theorem localTensorAction_eq_one_iff (f : localFiberSubgroup) :
    localTensorAction f = 1 ↔ f ∈ localDiagonalSubgroup := by
  constructor
  · intro hf
    let u₀ : SpinSpace := Pi.single 0 1
    let v₀ : Fin 24 → ℝ := Pi.single 0 1
    let a : ℝ := f.val.1.val u₀ 0
    let b : ℝ := f.val.2.val v₀ 0
    have hab : a * b = 1 := by
      simpa [a, b, u₀, v₀] using localTensorAction_trivial_pairing f hf u₀ v₀ 0 0
    have hS (u : SpinSpace) : f.val.1.val u = a • u := by
      funext t
      have h := localTensorAction_trivial_pairing f hf u v₀ t 0
      have hb : b ≠ 0 := by intro hb; simp [hb] at hab
      change f.val.1.val u t * b = u t * v₀ 0 at h
      simp only [v₀, Pi.single_eq_same, mul_one] at h
      change f.val.1.val u t = a * u t
      apply (mul_right_cancel₀ hb)
      calc
        f.val.1.val u t * b = u t := h
        _ = a * u t * b := by
          calc
            u t = (a * b) * u t := by rw [hab, one_mul]
            _ = a * u t * b := by ring
    have hE (v : Fin 24 → ℝ) : f.val.2.val v = b • v := by
      funext i
      have h := localTensorAction_trivial_pairing f hf u₀ v 0 i
      have ha : a ≠ 0 := by intro ha; simp [ha] at hab
      change a * f.val.2.val v i = u₀ 0 * v i at h
      simp only [u₀, Pi.single_eq_same, one_mul] at h
      change f.val.2.val v i = b * v i
      apply (mul_left_cancel₀ ha)
      calc
        a * f.val.2.val v i = v i := h
        _ = a * (b * v i) := by rw [← mul_assoc, hab, one_mul]
    have hnorm := f.val.1.property.2 u₀ u₀
    rw [hS] at hnorm
    have haa : a * a = 1 := by
      simpa [spinPairing, u₀, Pi.single_apply, mul_ite, ite_mul] using hnorm
    have ha : a = 1 ∨ a = -1 := mul_self_eq_one_iff.mp haa
    rcases ha with ha | ha
    · have hb : b = 1 := by simpa [ha] using hab
      refine ⟨0, ?_, ?_⟩ <;> intro x
      · simpa [ha] using hS x
      · simpa [hb] using hE x
    · have hb : b = -1 := by nlinarith [hab]
      refine ⟨1, ?_, ?_⟩ <;> intro x
      · simpa [ha, qSign] using hS x
      · simpa [hb, qSign] using hE x
  · exact localTensorAction_diagonal f

theorem coordinateGLTransport_injective {U V : Type*}
    [AddCommGroup U] [AddCommGroup V] [Module ℝ U] [Module ℝ V]
    (e : U ≃ₗ[ℝ] V) : Function.Injective (coordinateGLTransport e) := by
  intro a b hab
  apply LinearEquiv.ext
  intro x
  have h := congrArg (fun g : V ≃ₗ[ℝ] V => e.symm (g (e x))) hab
  change e.symm (e (a (e.symm (e x)))) = e.symm (e (b (e.symm (e x)))) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

theorem coordinateProdGLHom_apply {U V : Type*}
    [AddCommGroup U] [AddCommGroup V] [Module ℝ U] [Module ℝ V]
    (a : (U ≃ₗ[ℝ] U) × (V ≃ₗ[ℝ] V)) (x : U × V) :
    coordinateProdGLHom a x = (a.1 x.1, a.2 x.2) := rfl

theorem localConwayRawRepresentation_tensor (f : localFiberSubgroup)
    (x : ConwayRawSpace) :
    (localConwayRawRepresentation f x).2.2 = localTensorRepresentation f x.2.2 := by
  simp only [localConwayRawRepresentation, MonoidHom.comp_apply, MonoidHom.prod_apply,
    coordinateProdGLHom_apply]

theorem localGriessRepresentation_eq_one_iff (f : localFiberSubgroup) :
    localGriessRepresentation f = 1 ↔ f ∈ localDiagonalSubgroup := by
  constructor
  · intro hf
    have hc : localConwayRepresentation f = 1 := by
      apply LinearEquiv.ext
      intro x
      change localConwayRepresentation f x = x
      have h := congrArg (fun e : GriessSpace ≃ₗ[ℝ] GriessSpace =>
        griessConwayEquiv (e (griessConwayEquiv.symm x))) hf
      change griessConwayEquiv (griessConwayEquiv.symm
        (localConwayRepresentation f (griessConwayEquiv (griessConwayEquiv.symm x)))) =
        griessConwayEquiv (griessConwayEquiv.symm x) at h
      simpa only [LinearEquiv.apply_symm_apply] using h
    have ht : localTensorRepresentation f = 1 := by
      apply LinearEquiv.ext
      intro t
      let x : conwaySymmetricSpace := ⟨(0, (0, t)), by intro i j; rfl⟩
      have h := congrArg (fun e : conwaySymmetricSpace ≃ₗ[ℝ] conwaySymmetricSpace =>
        (e x).val.2.2) hc
      change (localConwayRawRepresentation f x.val).2.2 = x.val.2.2 at h
      rw [localConwayRawRepresentation_tensor] at h
      exact h
    apply (localTensorAction_eq_one_iff f).mp
    apply coordinateGLTransport_injective conwayTensorCoordinates
    change localTensorRepresentation f = coordinateGLTransport conwayTensorCoordinates 1
    rw [ht, map_one]
  · exact localGriessRepresentation_diagonal f

theorem localGriessRepresentation_ker :
    localGriessRepresentation.ker = localDiagonalSubgroup := by
  ext f
  exact localGriessRepresentation_eq_one_iff f

theorem rhoLocal_injective : Function.Injective rhoLocal := by
  apply (MonoidHom.ker_eq_bot_iff rhoLocal).mp
  ext h
  change rhoLocal h = 1 ↔ h = 1
  induction h using QuotientGroup.induction_on with
  | H f =>
    change localGriessRepresentation f = 1 ↔
      QuotientGroup.mk f = (1 : localFiberSubgroup ⧸ localDiagonalSubgroup)
    rw [QuotientGroup.eq_one_iff]
    exact localGriessRepresentation_eq_one_iff f

def qSection (v : Fin 24 → ZMod 2) : Q := ⟨ofAdd v, 1⟩

theorem qCentral_section (g : Q) :
    qCentral (toAdd g.coeff) * qSection (toAdd g.base) = g := by
  apply NormalizedCocycleExtension.Extension.ext
  · exact qCentral_mul_base _ _
  · apply Multiplicative.toAdd.injective
    rw [qCentral_mul_coeff]
    simp [qSection]

theorem spinConjugation_base_of_binary_trivial (s : SpinHolomorph)
    (hs : spinBinaryAction s = 1) (g : Q) :
    (spinConjugation s g).base = g.base := by
  have h := congrArg (fun e : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2) =>
    e (toAdd (qQuotHom g))) hs
  change qBinaryAction (spinConjugation s) (toAdd (qQuotHom g)) =
    toAdd (qQuotHom g) at h
  rw [qBinaryAction_apply] at h
  exact Multiplicative.toAdd.injective h

noncomputable def spinCentralPhase (s : SpinHolomorph) (v : Fin 24 → ZMod 2) : ZMod 2 :=
  toAdd (spinConjugation s (qSection v)).coeff

theorem spinConjugation_section (s : SpinHolomorph)
    (hs : spinBinaryAction s = 1) (v : Fin 24 → ZMod 2) :
    spinConjugation s (qSection v) = qCentral (spinCentralPhase s v) * qSection v := by
  rw [← qCentral_section (spinConjugation s (qSection v)),
    spinConjugation_base_of_binary_trivial s hs]
  rfl

theorem qSection_mul (v w : Fin 24 → ZMod 2) :
    qSection v * qSection w = qCentral (qBeta v w) * qSection (v + w) := by
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    rfl
  · apply Multiplicative.toAdd.injective
    rw [qCentral_mul_coeff]
    change (0 + 0) + qBeta v w = qBeta v w + 0
    simp

theorem spinCentralPhase_add (s : SpinHolomorph) (hs : spinBinaryAction s = 1)
    (v w : Fin 24 → ZMod 2) :
    spinCentralPhase s (v + w) = spinCentralPhase s v + spinCentralPhase s w := by
  have hv := spinConjugation_base_of_binary_trivial s hs (qSection v)
  have hw := spinConjugation_base_of_binary_trivial s hs (qSection w)
  have hl : toAdd (spinConjugation s (qSection v * qSection w)).coeff =
      qBeta v w + spinCentralPhase s (v + w) := by
    rw [qSection_mul, map_mul, spinConjugation_central, qCentral_mul_coeff]
    rfl
  have h := congrArg (fun q : Q => toAdd q.coeff)
    ((spinConjugation s).map_mul (qSection v) (qSection w))
  rw [hl] at h
  change qBeta v w + spinCentralPhase s (v + w) =
    (spinCentralPhase s v + spinCentralPhase s w) +
      qBeta (toAdd (spinConjugation s (qSection v)).base)
        (toAdd (spinConjugation s (qSection w)).base) at h
  rw [hv, hw] at h
  change qBeta v w + spinCentralPhase s (v + w) =
    (spinCentralPhase s v + spinCentralPhase s w) + qBeta v w at h
  rw [add_comm (spinCentralPhase s v + spinCentralPhase s w)] at h
  exact add_left_cancel h

noncomputable def spinCentralCharacter (s : SpinHolomorph) (hs : spinBinaryAction s = 1) :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  let e : (Fin 24 → ZMod 2) →+ ZMod 2 :=
    { toFun := spinCentralPhase s
      map_zero' := by simpa using spinCentralPhase_add s hs 0 0
      map_add' := spinCentralPhase_add s hs }
  { e with map_smul' := ZMod.map_smul e }


def qPolarLinear (v : Fin 24 → ZMod 2) :
    (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2 := qBilin v + qBilin.flip v

noncomputable def qDualVector (κ : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    Fin 24 → ZMod 2 :=
  fun j => Sum.elim (fun i => κ (Pi.single (Fin.natAdd 12 i) 1))
    (fun i => κ (Pi.single (Fin.castAdd 12 i) 1)) (finSumFinEquiv.symm j)

theorem qPolarLinear_dual (κ : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    qPolarLinear (qDualVector κ) = κ := by
  apply LinearMap.pi_ext
  intro i c
  have hsingle : Pi.single i c = c • (Pi.single i 1 : Fin 24 → ZMod 2) := by
    funext j
    simp [Pi.single_apply, smul_eq_mul]
  rw [hsingle, map_smul, map_smul]
  congr 1
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 12 ⊕ Fin 12 ≃ Fin 24).surjective i
  cases j with
  | inl j =>
    rw [finSumFinEquiv_apply_left]
    change qBeta (qDualVector κ) (Pi.single (Fin.castAdd 12 j) 1) +
      qBeta (Pi.single (Fin.castAdd 12 j) 1) (qDualVector κ) = _
    rw [qBeta_right_single_first, qBeta_single_first, zero_add]
    simp only [qDualVector, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
  | inr j =>
    rw [finSumFinEquiv_apply_right]
    change qBeta (qDualVector κ) (Pi.single (Fin.natAdd 12 j) 1) +
      qBeta (Pi.single (Fin.natAdd 12 j) 1) (qDualVector κ) = _
    rw [qBeta_single_second, qBeta_left_single_second, add_zero]
    simp only [qDualVector, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]

set_option backward.isDefEq.respectTransparency false in
theorem q_conjugation_central_phase (g k : Q) :
    g * k * g⁻¹ =
      qCentral (qBeta (toAdd g.base) (toAdd k.base) +
        qBeta (toAdd k.base) (toAdd g.base)) * k := by
  have h : g * k = qCentral (qBeta (toAdd g.base) (toAdd k.base) +
      qBeta (toAdd k.base) (toAdd g.base)) * k * g := by
    apply NormalizedCocycleExtension.Extension.ext
    · rw [NormalizedCocycleExtension.mul_base,
        NormalizedCocycleExtension.mul_base, qCentral_mul_base]
      exact mul_comm _ _
    · apply Multiplicative.toAdd.injective
      change (toAdd g.coeff + toAdd k.coeff) + qBeta (toAdd g.base) (toAdd k.base) =
        (toAdd (qCentral (qBeta (toAdd g.base) (toAdd k.base) +
          qBeta (toAdd k.base) (toAdd g.base)) * k).coeff + toAdd g.coeff) +
        qBeta (toAdd (qCentral (qBeta (toAdd g.base) (toAdd k.base) +
          qBeta (toAdd k.base) (toAdd g.base)) * k).base) (toAdd g.base)
      rw [qCentral_mul_coeff, qCentral_mul_base]
      have hz (a : ZMod 2) : a + a = 0 := by
        calc
          a + a = -a + a := congrArg (fun b => b + a) (ZMod.neg_eq_self_mod_two a).symm
          _ = 0 := neg_add_cancel a
      linear_combination -(hz (qBeta (toAdd k.base) (toAdd g.base)))
  rw [h, mul_assoc, mul_inv_cancel, mul_one]


theorem spinConjugation_binary_trivial_inner (s : SpinHolomorph)
    (hs : spinBinaryAction s = 1) :
    ∃ q : Q, spinConjugation s = spinConjugation (spinHolomorphIncl q) := by
  let κ := spinCentralCharacter s hs
  let q := qSection (qDualVector κ)
  refine ⟨q, ?_⟩
  apply MulEquiv.ext
  intro g
  rw [spinConjugation_incl, q_conjugation_central_phase]
  have hk : qBeta (toAdd q.base) (toAdd g.base) +
      qBeta (toAdd g.base) (toAdd q.base) = spinCentralPhase s (toAdd g.base) := by
    exact congrArg (fun l : (Fin 24 → ZMod 2) →ₗ[ZMod 2] ZMod 2 => l (toAdd g.base))
      (qPolarLinear_dual κ)
  rw [hk]
  apply NormalizedCocycleExtension.Extension.ext
  · rw [qCentral_mul_base]
    exact spinConjugation_base_of_binary_trivial s hs g
  · apply Multiplicative.toAdd.injective
    have h : spinConjugation s g = qCentral (toAdd g.coeff) *
        spinConjugation s (qSection (toAdd g.base)) := by
      conv_lhs => rw [← qCentral_section g]
      rw [map_mul, spinConjugation_central]
    rw [h, qCentral_mul_coeff, qCentral_mul_coeff]
    exact add_comm _ _

theorem spinBinaryAction_kernel_image (s : SpinHolomorph)
    (hs : spinBinaryAction s = 1) : ∃ q : Q, spinHolomorphIncl q = s := by
  obtain ⟨q, hq⟩ := spinConjugation_binary_trivial_inner s hs
  let r := s * (spinHolomorphIncl q)⁻¹
  have hr : r ∈ spinConjugation.ker := by
    change spinConjugation (s * (spinHolomorphIncl q)⁻¹) = 1
    rw [map_mul, map_inv, hq, mul_inv_cancel]
  obtain ⟨c, hc, he⟩ := spinHolomorph_conjugation_kernel_scalar ⟨r, hr⟩
  have hrq : ∃ d : ZMod 2, r = spinHolomorphIncl (qCentral d) := by
    rcases hc with hc | hc
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change r.val x = spinRepresentation (qCentral 0) x
      rw [spinRepresentation_central]
      simpa [hc] using he x
    · refine ⟨1, ?_⟩
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      change r.val x = spinRepresentation (qCentral 1) x
      rw [spinRepresentation_central]
      simpa [hc, qSign] using he x
  obtain ⟨d, hd⟩ := hrq
  refine ⟨qCentral d * q, ?_⟩
  rw [map_mul, ← hd]
  change s * (spinHolomorphIncl q)⁻¹ * spinHolomorphIncl q = s
  group


theorem leechBinaryAction_sign (e : leechIsomSubgroup) (he : e ∈ signsSubgroup) :
    leechBinaryAction e = 1 := by
  rcases he with he | he
  · have heq : e = 1 := Subtype.ext he
    rw [heq, map_one]
  · have hneg (u : leechIntegral) : leechIntegralAction e u = -u := by
      apply Subtype.ext
      apply leechCoordinateEmbedding_injective
      rw [leechIntegralAction_embedding, he]
      change -leechCoordinateEmbedding u.val = leechCoordinateEmbedding (-u.val)
      exact (map_neg leechCoordinateEmbedding u.val).symm
    apply LinearEquiv.ext
    intro v
    change leechBinaryAction e v = v
    obtain ⟨w, rfl⟩ := leechHyperbolicCoordinates.surjective v
    rw [leechBinaryAction_coordinates]
    apply congrArg leechHyperbolicCoordinates
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective twiceLeechIntegral w
    change leechReduction (leechIntegralAction e u) = leechReduction u
    rw [hneg, leechReduction_neg]

theorem inclQ_range_eq_projH_ker : inclQ.range = projH.ker := by
  apply le_antisymm inclQ_range_le_projH_ker
  intro h hh
  induction h using QuotientGroup.induction_on with
  | H f =>
    have he : f.val.2 ∈ signsSubgroup := by
      change QuotientGroup.mk f.val.2 = (1 : leechIsomSubgroup ⧸ signsSubgroup) at hh
      exact (QuotientGroup.eq_one_iff _).mp hh
    have hs : spinBinaryAction f.val.1 = 1 := by
      rw [f.property, leechBinaryAction_sign f.val.2 he]
    obtain ⟨q, hq⟩ := spinBinaryAction_kernel_image f.val.1 hs
    have hsign : ∃ c : ZMod 2, ∀ x, f.val.2.val x = qSign c • x := by
      rcases he with he | he
      · refine ⟨0, ?_⟩
        intro x
        rw [he]
        simp
      · refine ⟨1, ?_⟩
        intro x
        simpa [qSign] using he x
    obtain ⟨c, hc⟩ := hsign
    refine ⟨qCentral c * q, ?_⟩
    change QuotientGroup.mk (localFiberIncl (qCentral c * q)) = QuotientGroup.mk f
    apply Eq.symm
    apply QuotientGroup.eq.mpr
    refine ⟨c, ?_, ?_⟩
    · intro u
      change f.val.1.val.symm (spinRepresentation (qCentral c * q) u) = qSign c • u
      rw [map_mul, LinearEquiv.mul_apply, spinRepresentation_central]
      have hrep : spinRepresentation q = f.val.1.val := congrArg Subtype.val hq
      rw [hrep, map_smul, LinearEquiv.symm_apply_apply]
    · intro x
      change f.val.2.val.symm x = qSign c • x
      apply f.val.2.val.injective
      rw [LinearEquiv.apply_symm_apply, map_smul, hc, smul_smul, qSign_sq, one_smul]

theorem exists_spinHolomorph_lift (a : MulAut Q) (ha : ∀ c, a (qCentral c) = qCentral c) :
    ∃ s : SpinHolomorph, spinConjugation s = a := by
  obtain ⟨T, hT, he⟩ := exists_bijective_spin_intertwiner a ha
  let e := LinearEquiv.ofBijective T hT
  obtain ⟨s, hs, hi⟩ := exists_orthogonal_spin_intertwiner a e he
  obtain ⟨s', _, hsa⟩ := exists_spinHolomorph_of_implementation a s hi hs
  exact ⟨s', hsa⟩

theorem projH_surjective : Function.Surjective projH := by
  intro c
  obtain ⟨e, rfl⟩ := QuotientGroup.mk'_surjective signsSubgroup c
  let a := qBinaryIsometryLift (leechBinaryAction e) (leechBinaryAction_squareQuad e)
  obtain ⟨s, hs⟩ := exists_spinHolomorph_lift a
    (qBinaryIsometryLift_central (leechBinaryAction e) (leechBinaryAction_squareQuad e))
  have hf : (s, e) ∈ localFiberSubgroup := by
    change qBinaryAction (spinConjugation s) = leechBinaryAction e
    rw [hs]
    exact qBinaryAction_isometryLift (leechBinaryAction e) (leechBinaryAction_squareQuad e)
  refine ⟨QuotientGroup.mk ⟨(s, e), hf⟩, ?_⟩
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
