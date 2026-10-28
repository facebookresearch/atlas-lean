/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalInvariance
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness

/-! Faithfulness of the Conway group on the lattice quotient.

An isometry acting trivially modulo twice the Leech lattice fixes every
short class, hence acts by a sign on each short vector. Coordinate pair
vectors have a connected pattern of nonzero inner products and span the
ambient space, so all signs agree. Thus the kernel is exactly {±1}, and
the actual Conway quotient has a faithful binary representation. -/

@[expose] public section
open Multiplicative
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

noncomputable def leechUnit (i : Fin 24) : Fin 24 → ℝ := Pi.single i 1

lemma stdPairing_add_left (x y z : Fin 24 → ℝ) :
    stdPairingFun (x + y) z = stdPairingFun x z + stdPairingFun y z := by
  simp [stdPairingFun, add_mul, Finset.sum_add_distrib]
lemma stdPairing_add_right (x y z : Fin 24 → ℝ) :
    stdPairingFun x (y + z) = stdPairingFun x y + stdPairingFun x z := by
  simp [stdPairingFun, mul_add, Finset.sum_add_distrib]
lemma stdPairing_smul_left (a : ℝ) (x y : Fin 24 → ℝ) :
    stdPairingFun (a • x) y = a * stdPairingFun x y := by
  simp [stdPairingFun, mul_assoc, Finset.mul_sum]
lemma stdPairing_smul_right (a : ℝ) (x y : Fin 24 → ℝ) :
    stdPairingFun x (a • y) = a * stdPairingFun x y := by
  simp [stdPairingFun, mul_left_comm, Finset.mul_sum]
lemma stdPairing_unit_left (i : Fin 24) (x : Fin 24 → ℝ) :
    stdPairingFun (leechUnit i) x = x i := by
  simp [stdPairingFun, leechUnit, Pi.single_apply, ite_mul]

lemma leech_isometry_eigenvalue_agree (e : leechIsomSubgroup)
    (x y : Fin 24 → ℝ) (a b : ℝ) (ha : a * a = 1)
    (hx : e.val x = a • x) (hy : e.val y = b • y)
    (hxy : stdPairingFun x y ≠ 0) : a = b := by
  have h := e.property.1 x y
  rw [hx, hy, stdPairing_smul_left, stdPairing_smul_right] at h
  have hab : a * b = 1 := by
    apply mul_right_cancel₀ hxy
    simpa only [mul_assoc, one_mul] using h
  have ha0 : a ≠ 0 := by intro hz; simp [hz] at ha
  exact (mul_left_cancel₀ ha0) (ha.trans hab.symm)

lemma linear_isometry_pair_eigenvectors_scalar (e : leechIsomSubgroup)
    (hpair : ∀ i j : Fin 24, i ≠ j → ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
      e.val (leechUnit i + leechUnit j) = a • (leechUnit i + leechUnit j)) :
    ∃ a : ℝ, (a = 1 ∨ a = -1) ∧ ∀ x, e.val x = a • x := by
  obtain ⟨a, ha, h01⟩ := hpair 0 1 (by decide)
  have ha2 : a * a = 1 := by rcases ha with rfl|rfl <;> norm_num
  have h0i (i : Fin 24) (hi : i ≠ 0) :
      e.val (leechUnit 0 + leechUnit i) = a • (leechUnit 0 + leechUnit i) := by
    obtain ⟨b, hb, hbi⟩ := hpair 0 i hi.symm
    have hxy : stdPairingFun (leechUnit 0 + leechUnit 1)
        (leechUnit 0 + leechUnit i) ≠ 0 := by
      rw [stdPairing_add_left, stdPairing_unit_left, stdPairing_unit_left]
      by_cases hi1 : i = 1
      · subst i; norm_num [leechUnit, Pi.single_apply]
      · simp [leechUnit, hi.symm, Ne.symm hi1]
    have hab := leech_isometry_eigenvalue_agree e _ _ a b ha2 h01 hbi hxy
    rwa [← hab] at hbi
  have h12 : e.val (leechUnit 1 + leechUnit 2) = a • (leechUnit 1 + leechUnit 2) := by
    obtain ⟨b, hb, hbi⟩ := hpair 1 2 (by decide)
    have hxy : stdPairingFun (leechUnit 0 + leechUnit 1)
        (leechUnit 1 + leechUnit 2) ≠ 0 := by
      rw [stdPairing_add_left, stdPairing_unit_left, stdPairing_unit_left]
      norm_num [leechUnit, Pi.single_apply]
    have hab := leech_isometry_eigenvalue_agree e _ _ a b ha2 h01 hbi hxy
    rwa [← hab] at hbi
  have hsum : (leechUnit 0 + leechUnit 1) + (leechUnit 0 + leechUnit 2) -
      (leechUnit 1 + leechUnit 2) = (2:ℝ) • leechUnit 0 := by
    funext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h0 : e.val (leechUnit 0) = a • leechUnit 0 := by
    have h : e.val ((2:ℝ) • leechUnit 0) = a • ((2:ℝ) • leechUnit 0) := by
      rw [← hsum]
      simp only [map_sub, map_add, h01, h0i 2 (by decide), h12, smul_add, smul_sub]
    rw [map_smul] at h
    funext k
    have hk := congrFun h k
    change 2 * e.val (leechUnit 0) k = a * (2 * leechUnit 0 k) at hk
    change e.val (leechUnit 0) k = a * leechUnit 0 k
    nlinarith [hk]
  have hi (i : Fin 24) : e.val (leechUnit i) = a • leechUnit i := by
    by_cases hi : i = 0
    · subst i; exact h0
    · have h := h0i i hi
      rw [map_add, h0, smul_add] at h
      exact add_left_cancel h
  have hl : e.val.toLinearMap = a • (LinearMap.id : (Fin 24 → ℝ) →ₗ[ℝ] (Fin 24 → ℝ)) := by
    apply LinearMap.pi_ext
    intro i c
    have hs : (Pi.single i c : Fin 24 → ℝ) = c • leechUnit i := by
      funext k
      simp [leechUnit, Pi.single_apply, smul_eq_mul]
    rw [hs, map_smul]
    change c • e.val (leechUnit i) = a • (c • leechUnit i)
    rw [hi]
    exact smul_comm _ _ _
  refine ⟨a, ha, ?_⟩
  intro x
  exact congrArg (fun t : (Fin 24 → ℝ) →ₗ[ℝ] (Fin 24 → ℝ) => t x) hl

lemma griessShortPermutation_binary_trivial (e : leechIsomSubgroup)
    (he : leechBinaryAction e = 1) (r : GriessShortIndex) : griessShortPermutation e r = r := by
  apply griessShortClass_injective
  apply leechHyperbolicCoordinates.injective
  rw [griessShortPermutation_class, ← leechBinaryAction_coordinates, he]
  rfl

lemma leech_pair_vector_short (i j : Fin 24) (hij : i ≠ j) :
    griessShortVector (Sum.inl (1, griessPairIndex i j hij)) =
      (4 / Real.sqrt 8) • (leechUnit i + leechUnit j) := by
  funext k
  simp only [griessShortVector, griessShortIntegral, griessPairIndex_coordinates,
    show (1 : Fin 2) ≠ 0 by decide, ite_false]
  by_cases hlt : i < j
  · simp only [ite_eq_left hlt, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul, leechUnit, Pi.single_apply]
    push_cast
    simp only [eq_comm]
    ring
  · simp only [ite_eq_right hlt, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul, leechUnit, Pi.single_apply]
    push_cast
    simp only [eq_comm]
    ring

theorem leechBinaryAction_mem_kernel_iff_sign (e : leechIsomSubgroup) :
    leechBinaryAction e = 1 ↔ e ∈ signsSubgroup := by
  constructor
  · intro he
    have hpair : ∀ i j : Fin 24, i ≠ j → ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
        e.val (leechUnit i + leechUnit j) = a • (leechUnit i + leechUnit j) := by
      intro i j hij
      let r : GriessShortIndex := Sum.inl (1, griessPairIndex i j hij)
      have h := griessShortPermutation_vector e r
      rw [griessShortPermutation_binary_trivial e he] at h
      change e.val (griessShortVector (Sum.inl (1, griessPairIndex i j hij))) = _ ∨
        e.val (griessShortVector (Sum.inl (1, griessPairIndex i j hij))) = _ at h
      rw [leech_pair_vector_short] at h
      have hc : (4 / Real.sqrt 8 : ℝ) ≠ 0 := div_ne_zero (by norm_num)
        (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
      rcases h with h | h
      · refine ⟨1, Or.inl rfl, ?_⟩
        rw [map_smul] at h
        simpa only [one_smul] using (smul_right_injective _ hc) h
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [map_smul, ← smul_neg] at h
        simpa only [neg_one_smul] using (smul_right_injective _ hc) h
    obtain ⟨a, ha, heq⟩ := linear_isometry_pair_eigenvectors_scalar e hpair
    rcases ha with ha | ha
    · left
      apply LinearEquiv.ext
      intro x
      simpa [ha] using heq x
    · right
      intro x
      simpa [ha] using heq x
  · exact leechBinaryAction_sign e

theorem leechBinaryAction_ker : leechBinaryAction.ker = signsSubgroup := by
  ext e
  exact leechBinaryAction_mem_kernel_iff_sign e

/-- The actual Conway quotient acts on the genuine lattice quotient. -/
noncomputable def co1BinaryAction : Co1 →*
    ((Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) :=
  QuotientGroup.lift signsSubgroup leechBinaryAction (by rw [leechBinaryAction_ker])

/-- Quotienting by precisely the signs makes the binary action faithful. -/
theorem co1BinaryAction_injective : Function.Injective co1BinaryAction := by
  apply (MonoidHom.ker_eq_bot_iff co1BinaryAction).mp
  ext h
  change co1BinaryAction h = 1 ↔ h = 1
  induction h using QuotientGroup.induction_on with
  | H e =>
    change leechBinaryAction e = 1 ↔
      QuotientGroup.mk e = (1 : leechIsomSubgroup ⧸ signsSubgroup)
    rw [QuotientGroup.eq_one_iff]
    exact leechBinaryAction_mem_kernel_iff_sign e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
