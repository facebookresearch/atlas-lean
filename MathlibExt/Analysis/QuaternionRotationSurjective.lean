/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.QuaternionRotation

/-!
# Surjectivity of the unit-quaternion rotation action

Every special orthogonal `3 × 3` matrix is the rotation matrix of a unit
quaternion. Third-column alignment sends any unit vector to the third column
of some `rotMatrix`; a rotation whose third column is `e₂` is planar; and
each planar rotation is `rotMatrix` of a half-angle quaternion about the
third axis. Together with the kernel computation in
`MathlibExt.Analysis.QuaternionRotation`, this completes the double cover of
`SO(3)` by unit quaternions.

References: J. Stillwell, *Naive Lie Theory* (Springer UTM, 2008), §1.5 and
§2.3 (the groups SU(2) and SO(3)).
-/

@[expose] public section

open Quaternion

namespace QuaternionRotation

/-- Build a unit quaternion from `normSq q = 1`. -/
private def mk_unitary_of_normSq_eq_one {q : ℍ} (hq : normSq q = 1) : unitary ℍ :=
  ⟨q, Unitary.mem_iff.mpr ⟨by rw [Quaternion.star_mul_self, hq, Quaternion.coe_one],
    by rw [Quaternion.self_mul_star, hq, Quaternion.coe_one]⟩⟩

/-- The coercion of `mk_unitary_of_normSq_eq_one` is the quaternion itself. -/
private theorem coe_mk_unitary_of_normSq_eq_one {q : ℍ} (hq : normSq q = 1) :
    ((mk_unitary_of_normSq_eq_one hq : unitary ℍ) : ℍ) = q := rfl

/-- Every unit vector is the third column of `rotMatrix u` for some unit
quaternion `u`: if `n 2 = -1` take `i`; otherwise the half-angle quaternion
`⟨w, -n 1/(2w), n 0/(2w), 0⟩` with `w = √((1 + n 2)/2)`. -/
theorem exists_rotMatrix_apply_two (n : Fin 3 → ℝ)
    (hn : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1) :
    ∃ u : unitary ℍ, ∀ i, rotMatrix (u : ℍ) i 2 = n i := by
  by_cases h2 : n 2 = -1
  · have h0 : n 0 = 0 := by nlinarith
    have h1 : n 1 = 0 := by nlinarith
    have hN : normSq (⟨0, 1, 0, 0⟩ : ℍ) = 1 := by
      rw [Quaternion.normSq_def']
      norm_num
    refine ⟨mk_unitary_of_normSq_eq_one hN, fun i => ?_⟩
    rw [coe_mk_unitary_of_normSq_eq_one]
    fin_cases i <;> simp [rotMatrix, imCoords, imBasis, h0, h1, h2]
  · have hpos : 0 < 1 + n 2 := by
      rcases (show -1 ≤ n 2 by nlinarith).lt_or_eq with h | h
      · linarith
      · exact absurd h.symm h2
    have h1n2 : (1 : ℝ) + n 2 ≠ 0 := ne_of_gt hpos
    set w := √((1 + n 2) / 2) with hw_def
    have hw2 : w ^ 2 = (1 + n 2) / 2 := Real.sq_sqrt (by positivity)
    have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
    have hwne : w ≠ 0 := ne_of_gt hwpos
    have hw2ne : (2 : ℝ) * w ≠ 0 := by positivity
    set a := -n 1 / (2 * w) with ha_def
    set b := n 0 / (2 * w) with hb_def
    have hwa : 2 * w * a = -n 1 := by rw [ha_def]; field_simp
    have hwb : 2 * w * b = n 0 := by rw [hb_def]; field_simp
    have hab2 : a ^ 2 + b ^ 2 = (1 - n 2) / 2 := by
      have hsq : (2 * w * a) ^ 2 + (2 * w * b) ^ 2 = n 0 ^ 2 + n 1 ^ 2 := by
        rw [hwa, hwb]; ring
      have hmul := congrArg (fun t => 2 * (a ^ 2 + b ^ 2) * t) hw2
      have hcancel : (1 + n 2) * (a ^ 2 + b ^ 2) = (1 - n 2 ^ 2) / 2 := by
        linarith [hsq, hmul, hn]
      have hfactor : (1 - n 2 ^ 2) / 2 = (1 + n 2) * ((1 - n 2) / 2) := by ring
      rw [hfactor] at hcancel
      exact mul_left_cancel₀ h1n2 hcancel
    have hN : normSq (⟨w, a, b, 0⟩ : ℍ) = 1 := by
      simp [Quaternion.normSq_def']
      linarith [hw2, hab2]
    refine ⟨mk_unitary_of_normSq_eq_one hN, fun i => ?_⟩
    rw [coe_mk_unitary_of_normSq_eq_one]
    have e0 : rotMatrix (⟨w, a, b, 0⟩ : ℍ) 0 2 = 2 * w * b := by
      simp [rotMatrix, imCoords, imBasis]; ring
    have e1 : rotMatrix (⟨w, a, b, 0⟩ : ℍ) 1 2 = -(2 * w * a) := by
      simp [rotMatrix, imCoords, imBasis]; ring
    have e2 : rotMatrix (⟨w, a, b, 0⟩ : ℍ) 2 2 = w ^ 2 - a ^ 2 - b ^ 2 := by
      simp [rotMatrix, imCoords, imBasis]; ring
    fin_cases i
    · simp [e0, hwb]
    · simp [e1, hwa]
    · simp [e2]; linarith [hw2, hab2]

/-- A rotation whose third column is `e₂` is a planar rotation in the first
two coordinates. -/
theorem eq_of_apply_two {B : Matrix (Fin 3) (Fin 3) ℝ}
    (hB : B ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (h : ∀ i, B i 2 = if i = 2 then 1 else 0) :
    B = !![B 0 0, B 0 1, 0; -B 0 1, B 0 0, 0; 0, 0, 1] := by
  obtain ⟨horth, hdet⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hB
  have h2 : Matrix.transpose B * B = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp horth
  have e : ∀ i j, (Matrix.transpose B * B) i j = if i = j then 1 else 0 := fun i j => by
    rw [h2, Matrix.one_apply]
  have h02 := e 0 2
  have h12 := e 1 2
  have h00 := e 0 0
  have h11 := e 1 1
  have h01 := e 0 1
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, h] at h02 h12 h00 h11 h01
  rw [Matrix.det_fin_three] at hdet
  simp only [h] at hdet
  norm_num at h02 h12 h00 h11 h01 hdet
  have h3 : (B 1 1 - B 0 0) ^ 2 + (B 1 0 + B 0 1) ^ 2 = 0 := by
    simp only [h02, h12] at h00 h11 h01 hdet
    nlinarith
  have h4 : B 1 1 = B 0 0 := by nlinarith
  have h5 : B 1 0 = -B 0 1 := by nlinarith
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h, h02, h12, h4, h5]

/-- Every planar rotation matrix is `rotMatrix` of a unit quaternion
(a half-angle about the third axis). -/
theorem exists_unitary_rotMatrix_eq_planar {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ u : unitary ℍ, rotMatrix (u : ℍ) = !![c, s, 0; -s, c, 0; 0, 0, 1] := by
  by_cases hc : c = -1
  · have hs : s = 0 := by nlinarith
    have hN : normSq (⟨0, 0, 0, 1⟩ : ℍ) = 1 := by
      rw [Quaternion.normSq_def']
      norm_num
    refine ⟨mk_unitary_of_normSq_eq_one hN, ?_⟩
    rw [coe_mk_unitary_of_normSq_eq_one, hc, hs]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [rotMatrix, imCoords, imBasis]
  · have hpos : 0 < 1 + c := by
      rcases (show -1 ≤ c by nlinarith).lt_or_eq with h | h
      · linarith
      · exact absurd h.symm hc
    have h1c : (1 : ℝ) + c ≠ 0 := ne_of_gt hpos
    set w := √((1 + c) / 2) with hw_def
    have hw2 : w ^ 2 = (1 + c) / 2 := Real.sq_sqrt (by positivity)
    have hwpos : 0 < w := Real.sqrt_pos.mpr (by positivity)
    have hwne : w ≠ 0 := ne_of_gt hwpos
    have hw2ne : (2 : ℝ) * w ≠ 0 := by positivity
    set z := -s / (2 * w) with hz_def
    have hzw : 2 * w * z = -s := by rw [hz_def]; field_simp
    have hz2 : z ^ 2 = (1 - c) / 2 := by
      have hsq : (2 * w * z) ^ 2 = s ^ 2 := by rw [hzw]; ring
      have hmul := congrArg (fun t => 2 * z ^ 2 * t) hw2
      have hcancel : (1 + c) * z ^ 2 = (1 - c ^ 2) / 2 := by linarith [hsq, hmul, hcs]
      have hfactor : (1 - c ^ 2) / 2 = (1 + c) * ((1 - c) / 2) := by ring
      rw [hfactor] at hcancel
      exact mul_left_cancel₀ h1c hcancel
    have hN : normSq (⟨w, 0, 0, z⟩ : ℍ) = 1 := by
      simp [Quaternion.normSq_def']
      linarith [hw2, hz2]
    refine ⟨mk_unitary_of_normSq_eq_one hN, ?_⟩
    rw [coe_mk_unitary_of_normSq_eq_one]
    ext a b
    fin_cases a <;> fin_cases b
    · simp [rotMatrix, imCoords, imBasis]; linarith [hw2, hz2]
    · simp [rotMatrix, imCoords, imBasis]; linarith [hzw]
    · simp [rotMatrix, imCoords, imBasis]
    · simp [rotMatrix, imCoords, imBasis]; linarith [hzw]
    · simp [rotMatrix, imCoords, imBasis]; linarith [hw2, hz2]
    · simp [rotMatrix, imCoords, imBasis]
    · simp [rotMatrix, imCoords, imBasis]
    · simp [rotMatrix, imCoords, imBasis]
    · simp [rotMatrix, imCoords, imBasis]; linarith [hw2, hz2]

/-- **Unit quaternions double-cover `SO(3)`**: the conjugation action of unit
quaternions on pure imaginary quaternions reaches every special orthogonal
matrix. (Stillwell, Naive Lie Theory, §1.5 and §2.3.) -/
theorem unitaryHomSpecialOrthogonalGroup_surjective :
    Function.Surjective unitaryHomSpecialOrthogonalGroup := by
  intro A
  set S : Matrix (Fin 3) (Fin 3) ℝ := (A : Matrix (Fin 3) (Fin 3) ℝ) with hS_def
  have hS : S ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := A.2
  obtain ⟨horthS, hdetS⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hS
  have hStS : Matrix.transpose S * S = 1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp horthS
  have hcol : S 0 2 ^ 2 + S 1 2 ^ 2 + S 2 2 ^ 2 = 1 := by
    have e22 : (Matrix.transpose S * S) 2 2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) 2 2 :=
      congrFun (congrFun hStS 2) 2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] at e22
    simpa [pow_two] using e22
  obtain ⟨u, hu⟩ := exists_rotMatrix_apply_two (fun i => S i 2) hcol
  have hu' : ∀ i, rotMatrix (u : ℍ) i 2 = S i 2 := hu
  set R : Matrix (Fin 3) (Fin 3) ℝ := rotMatrix (u : ℍ) with hR_def
  have hN : Quaternion.normSq (u : ℍ) = 1 := by
    have hnorm := CStarRing.norm_coe_unitary u
    rw [Quaternion.normSq_eq_norm_mul_self, hnorm, mul_one]
  have hRtR : Matrix.transpose R * R = 1 := by
    have hgen := rotMatrix_transpose_mul_self (u : ℍ)
    rw [hN, one_pow, one_smul] at hgen
    exact hgen
  have hRmem : R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
    rotMatrix_mem_specialOrthogonalGroup (CStarRing.norm_coe_unitary u)
  obtain ⟨horthR, hdetR⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp hRmem
  have hRRt : R * Matrix.transpose R = 1 := (Matrix.mem_orthogonalGroup_iff _ _).mp horthR
  set T : Matrix (Fin 3) (Fin 3) ℝ := Matrix.transpose R * S with hT_def
  have hTmem : T ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
    have hRtmem : Matrix.transpose R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
      rw [Matrix.mem_specialOrthogonalGroup_iff]
      constructor
      · rw [Matrix.mem_orthogonalGroup_iff']
        rw [Matrix.transpose_transpose]
        exact hRRt
      · rw [Matrix.det_transpose]
        exact hdetR
    have hmem := mul_mem hRtmem hS
    rw [← hT_def] at hmem
    exact hmem
  have hTcol : ∀ i, T i 2 = if i = 2 then 1 else 0 := by
    intro i
    rw [hT_def]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
    rw [← hu' 0, ← hu' 1, ← hu' 2]
    have e : (Matrix.transpose R * R) i 2 = (1 : Matrix (Fin 3) (Fin 3) ℝ) i 2 :=
      congrFun (congrFun hRtR i) 2
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three,
      Matrix.one_apply] at e
    exact e
  have hTeq := eq_of_apply_two hTmem hTcol
  have hcs : T 0 0 ^ 2 + T 0 1 ^ 2 = 1 := by
    have hTtT : Matrix.transpose T * T = 1 :=
      (Matrix.mem_orthogonalGroup_iff' _ _).mp
        (Matrix.mem_specialOrthogonalGroup_iff.mp hTmem).1
    have e00 : (Matrix.transpose T * T) 0 0 = (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 0 :=
      congrFun (congrFun hTtT 0) 0
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] at e00
    have f10 : T 1 0 = -T 0 1 := by rw [hTeq]; simp
    have f20 : T 2 0 = 0 := by rw [hTeq]; simp
    rw [f10, f20] at e00
    simpa [pow_two] using e00
  obtain ⟨v, hv⟩ := exists_unitary_rotMatrix_eq_planar hcs
  refine ⟨u * v, ?_⟩
  apply Subtype.ext
  show rotMatrix ((u * v : unitary ℍ) : ℍ) = S
  have hmul : ((u * v : unitary ℍ) : ℍ) = (u : ℍ) * (v : ℍ) := rfl
  rw [hmul, rotMatrix_mul, hv, ← hTeq, ← hR_def, hT_def, ← mul_assoc, hRRt, one_mul]

end QuaternionRotation
