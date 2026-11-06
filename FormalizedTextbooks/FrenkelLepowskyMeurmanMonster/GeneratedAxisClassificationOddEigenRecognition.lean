/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddStatePairing

/-! Actual common pair-short eigenvectors of norm two are precisely the
actual extraspecial orbit of the distinguished Hadamard state. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem insert_add_omega (a : Fin 11 → ZMod 2) :
    generatedOddSpinInsert a 0 + (Pi.single (11 : Fin 12) 1 : SpinIndex) =
      generatedOddSpinInsert a 1 := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · change generatedOddSpinInsert a 0 11 + 1 = generatedOddSpinInsert a 1 11
    rw [generatedOddSpinInsert_last, generatedOddSpinInsert_last, zero_add]
  · have hi : i.castSucc ≠ (11 : Fin 12) := by
      intro h
      have he := congrArg Fin.val h
      change i.val = 11 at he
      omega
    change generatedOddSpinInsert a 0 i.castSucc +
      (Pi.single (11 : Fin 12) 1 : SpinIndex) i.castSucc =
        generatedOddSpinInsert a 1 i.castSucc
    rw [Pi.single_eq_of_ne hi]
    have h0 := congrFun (generatedOddSpinInsert_low a 0) i
    have h1 := congrFun (generatedOddSpinInsert_low a 1) i
    change generatedOddSpinInsert a 0 i.castSucc = a i at h0
    change generatedOddSpinInsert a 1 i.castSucc = a i at h1
    rw [h0, h1, add_zero]

/-- A common actual pair eigenvector lies in one signed Hadamard line. -/
theorem generatedOddSpin_common_eigen_line (v : SpinSpace) (a : Fin 276 → ℝ)
    (hminus : ∀ p, spinOperator (griessShortQ (Sum.inl (0, p))) v = a p • v)
    (b : ZMod 2)
    (hplus : spinOperator (griessShortQ (Sum.inl (1, 0))) v = qSign b • v)
    (u : SpinIndex) (hu : v u ≠ 0) :
    ∃ w : Fin 11 → ZMod 2, ∃ e : ZMod 2, ∃ z : ℝ,
      v = z • generatedOddSpinState w e 0 := by
  let w := generatedOddSpinLow u
  let k := golayEncoder (generatedOddSpinInsert w 0) (griessCoordinatePair 0).1 +
    golayEncoder (generatedOddSpinInsert w 0) (griessCoordinatePair 0).2
  let e := k + b
  let z := v (generatedOddSpinInsert w 0)
  have he : v (generatedOddSpinInsert w 1) = qSign e * z := by
    have hh := congrFun hplus (generatedOddSpinInsert w 0)
    rw [spinOperator_griessPairPlus, insert_add_omega] at hh
    change qSign k * v (generatedOddSpinInsert w 1) = qSign b * z at hh
    have hm := congrArg (fun x : ℝ => qSign k * x) hh
    rw [← mul_assoc, qSign_sq, one_mul] at hm
    rw [show e = k + b from rfl, qSign_add]
    nlinarith only [hm]
  refine ⟨w, e, z, ?_⟩
  ext t
  by_cases ht : generatedOddSpinLow t = w
  · have hb : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide +kernel
    rcases hb (t 11) with hz | hz
    · have hcoord : t = generatedOddSpinInsert w 0 := by
        rw [← generatedOddSpinInsert_reconstruct t, ht, hz]
      subst t
      simp [generatedOddSpinState, generatedOddSpinInsert_low, generatedOddSpinInsert_last, z]
    · have hcoord : t = generatedOddSpinInsert w 1 := by
        rw [← generatedOddSpinInsert_reconstruct t, ht, hz]
      subst t
      rw [he]
      simp [generatedOddSpinState, generatedOddSpinInsert_low, generatedOddSpinInsert_last,
        mul_comm]
  · have hz := generatedOddSpin_common_eigen_zero v a hminus u hu t ht
    simp [generatedOddSpinState, ht, hz]

/-- Norm two and all actual pair-short eigenvalue relations force membership in
 the actual Q orbit, including the global sign. -/
theorem generatedOddSpin_common_eigen_Q_orbit (v : SpinSpace)
    (hn : spinPairing v v = 2)
    (hminus : ∀ p : Fin 276, ∃ b : ZMod 2,
      spinOperator (griessShortQ (Sum.inl (0, p))) v = qSign b • v)
    (hplus : ∃ b : ZMod 2,
      spinOperator (griessShortQ (Sum.inl (1, 0))) v = qSign b • v) :
    ∃ q : Q, spinOperator q (generatedOddSpinState 0 1 0) = v := by
  classical
  have hv : v ≠ 0 := by
    intro hz
    rw [hz] at hn
    simp [spinPairing] at hn
  obtain ⟨u, hu⟩ : ∃ u : SpinIndex, v u ≠ 0 := by
    by_contra h
    apply hv
    ext t
    exact not_ne_iff.mp (not_exists.mp h t)
  choose a ha using hminus
  obtain ⟨b, hb⟩ := hplus
  obtain ⟨w, e, z, he⟩ := generatedOddSpin_common_eigen_line v (fun p => qSign (a p)) ha b hb u hu
  have hz : z = 1 ∨ z = -1 := by
    rw [he, spinPairing_smul_left, spinPairing_smul_right,
      generatedOddSpinState_pairing] at hn
    apply sq_eq_one_iff.mp
    nlinarith
  rcases hz with hz | hz
  · refine ⟨generatedOddSpinQ w e 0, ?_⟩
    rw [generatedOddSpinQ_state, he, hz, one_smul]
  · refine ⟨generatedOddSpinQ w e 1, ?_⟩
    rw [generatedOddSpinQ_state, he, hz]
    ext t
    simp only [generatedOddSpinState, Pi.smul_apply, smul_eq_mul, qSign_add, qSign_one,
      zero_add]
    split_ifs <;> ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
