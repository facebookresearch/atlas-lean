/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexCoordinateBethe

open Finset Matrix

namespace StatMech.FrontierD

noncomputable section

instance : Unique (Equiv.Perm (Fin 1)) where
  default := 1
  uniq σ := by
    ext i
    fin_cases i
    simp


def sixVertexSingletonSector {N : ℕ} (i : Fin N) : SixVertexSector N 1 :=
  ⟨{i}, by simp⟩

@[simp] theorem sixVertexSectorPosition_singleton {N : ℕ} (i : Fin N) :
    sixVertexSectorPosition (sixVertexSingletonSector i) 0 = i := by
  have hmem := sixVertexSectorPosition_mem (sixVertexSingletonSector i) (0 : Fin 1)
  simpa [sixVertexSingletonSector] using hmem

theorem sixVertexSector_eq_singleton_position {N : ℕ}
    (x : SixVertexSector N 1) :
    x = sixVertexSingletonSector (sixVertexSectorPosition x 0) := by
  apply Subtype.ext
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp x.prop
  have hmem := sixVertexSectorPosition_mem x (0 : Fin 1)
  have hpos : sixVertexSectorPosition x 0 = i := by simpa [hi] using hmem
  simp [sixVertexSingletonSector, hi, hpos]


def sixVertexOneSectorEquiv (N : ℕ) : SixVertexSector N 1 ≃ Fin N where
  toFun x := sixVertexSectorPosition x 0
  invFun := sixVertexSingletonSector
  left_inv := fun x => (sixVertexSector_eq_singleton_position x).symm
  right_inv := sixVertexSectorPosition_singleton

theorem sixVertexOne_interlaced {N : ℕ} (x y : SixVertexSector N 1) :
    SixVertexInterlaced (sixVertexSectorRow x) (sixVertexSectorRow y) := by
  rcases le_total (sixVertexSectorPosition x 0)
      (sixVertexSectorPosition y 0) with hxy | hyx
  · left
    apply sixVertexForwardInterlaced_of_positions
    constructor
    · intro i
      fin_cases i
      exact hxy
    · intro k hk
      omega
  · right
    apply sixVertexForwardInterlaced_of_positions
    constructor
    · intro i
      fin_cases i
      exact hyx
    · intro k hk
      omega

theorem sixVertexOne_rowDistance_eq_two {N : ℕ}
    {x y : SixVertexSector N 1} (hxy : x ≠ y) :
    sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) = 2 := by
  let px := sixVertexSectorPosition x 0
  let py := sixVertexSectorPosition y 0
  have hx : (x : Finset (Fin N)) = {px} := by
    simpa [px, sixVertexSingletonSector] using
      congrArg Subtype.val (sixVertexSector_eq_singleton_position x)
  have hy : (y : Finset (Fin N)) = {py} := by
    simpa [py, sixVertexSingletonSector] using
      congrArg Subtype.val (sixVertexSector_eq_singleton_position y)
  have hp : px ≠ py := by
    intro hp
    apply hxy
    apply Subtype.ext
    simp [hx, hy, hp]
  unfold sixVertexRowDistance
  have hfilter :
      ({i | sixVertexSectorRow x i ≠ sixVertexSectorRow y i} :
        Finset (Fin N)) = {px, py} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    have hlogic : ¬(i = px ↔ i = py) ↔ i = px ∨ i = py := by
      constructor
      · intro h
        by_cases hix : i = px
        · exact Or.inl hix
        by_cases hiy : i = py
        · exact Or.inr hiy
        exfalso
        apply h
        constructor <;> intro hi <;> contradiction
      · rintro (hix | hiy) hiff
        · apply hp
          calc
            px = i := hix.symm
            _ = py := hiff.mp hix
        · apply hp
          calc
            px = i := (hiff.mpr hiy).symm
            _ = py := hiy
    simpa [sixVertexSectorRow, hx, hy] using hlogic
  rw [hfilter, Finset.card_pair hp]

theorem sixVertexSectorTransfer_one_apply {N : ℕ} (c : ℝ)
    (x y : SixVertexSector N 1) :
    sixVertexSectorTransfer N 1 c x y = if x = y then 2 else c ^ 2 := by
  classical
  by_cases hxy : x = y
  · simp [hxy, sixVertexSectorTransfer, sixVertexTransfer]
  · have hrow : sixVertexSectorRow x ≠ sixVertexSectorRow y := by
      intro h
      apply hxy
      apply Subtype.ext
      ext i
      have hi := congrFun h i
      simpa [sixVertexSectorRow] using hi
    simp [sixVertexSectorTransfer, sixVertexTransfer, hrow,
      sixVertexOne_interlaced x y, sixVertexOne_rowDistance_eq_two hxy, hxy]

@[simp] theorem sixVertexBetheAmplitude_one (c : ℝ) (p : Fin 1 → ℝ)
    (σ : Equiv.Perm (Fin 1)) : sixVertexBetheAmplitude c p σ = 1 := by
  rw [Subsingleton.elim σ 1]
  simp [sixVertexBetheAmplitude, sixVertexBethePairProduct]

@[simp] theorem sixVertexCoordinateBetheWave_one {N : ℕ} (c : ℝ)
    (p : Fin 1 → ℝ) (x : SixVertexSector N 1) :
    sixVertexCoordinateBetheWave c p x =
      sixVertexBethePhase (p 0) ^ (sixVertexSectorPosition x 0).val := by
  simp [sixVertexCoordinateBetheWave, sixVertexBetheMonomial]

theorem sixVertexBetheEigenvalueCandidate_one {c : ℝ} (p : Fin 1 → ℝ)
    (hphase : sixVertexBethePhase (p 0) ≠ 1) :
    sixVertexBetheEigenvalueCandidate c p = 2 - c ^ 2 := by
  simp [sixVertexBetheEigenvalueCandidate, sixVertexBetheL,
    sixVertexBetheM]
  have hden : (1 : ℂ) - sixVertexBethePhase (p 0) ≠ 0 :=
    sub_ne_zero.mpr hphase.symm
  field_simp [hden]
  ring

theorem sum_sixVertexBethePhase_pow_eq_zero {N : ℕ} {p : ℝ}
    (hphase : sixVertexBethePhase p ≠ 1)
    (hperiodic : sixVertexBethePhase p ^ N = 1) :
    ∑ i : Fin N, sixVertexBethePhase p ^ i.val = 0 := by
  rw [Finset.sum_fin_eq_sum_range]
  have hrewrite :
      (∑ i ∈ Finset.range N,
        if h : i < N then sixVertexBethePhase p ^ (⟨i, h⟩ : Fin N).val else 0) =
        ∑ i ∈ Finset.range N, sixVertexBethePhase p ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [dif_pos (Finset.mem_range.mp hi)]
  have hgeom := geom_sum_mul (sixVertexBethePhase p) N
  rw [hperiodic, sub_self] at hgeom
  rw [hrewrite]
  exact (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hphase)

theorem sixVertexMultiplicativeBethe_one_periodic {c : ℝ} {N : ℕ}
    (p : Fin 1 → ℝ)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N 1 p) :
    sixVertexBethePhase (p 0) ^ N = 1 := by
  have hp0 := hp (0 : Fin 1)
  have hexp :
      Complex.exp (Complex.I * (((N : ℝ) * p 0 : ℝ) : ℂ)) = 1 := by
    simpa [sixVertexTheta_self] using hp0
  rw [sixVertexBethePhase]
  rw [← Complex.exp_nat_mul]
  convert hexp using 1
  push_cast
  ring_nf

theorem sixVertexBethePhase_ne_one_of_mem_Ioo
    {p : ℝ} (hp : p ∈ Set.Ioo (-Real.pi) Real.pi) (hp0 : p ≠ 0) :
    sixVertexBethePhase p ≠ 1 := by
  intro hphase
  rw [sixVertexBethePhase] at hphase
  rcases Complex.exp_eq_one_iff.mp hphase with ⟨m, hm⟩
  have him := congrArg Complex.im hm
  norm_num at him
  have htwopi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmlo : (-1 : ℝ) < (m : ℝ) := by
    by_contra h
    have hmle : (m : ℝ) ≤ -1 := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_right hmle htwopi.le
    rw [← him] at hmul
    linarith [hp.1, Real.pi_pos]
  have hmhi : (m : ℝ) < 1 := by
    by_contra h
    have hmge : (1 : ℝ) ≤ m := le_of_not_gt h
    have hmul := mul_le_mul_of_nonneg_right hmge htwopi.le
    rw [← him] at hmul
    linarith [hp.2, Real.pi_pos]
  have hmlo' : (-1 : ℤ) < m := by exact_mod_cast hmlo
  have hmhi' : m < (1 : ℤ) := by exact_mod_cast hmhi
  have hm0 : m = 0 := by omega
  subst m
  exact hp0 (by simpa only [Int.cast_zero, zero_mul] using him)




theorem sixVertexCoordinateBetheEigenrelation_one
    {N : ℕ} (c : ℝ) (p : Fin 1 → ℝ)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N 1 p)
    (hphase : sixVertexBethePhase (p 0) ≠ 1) :
    SixVertexCoordinateBetheEigenrelation (N := N) c p := by
  classical
  let z := sixVertexBethePhase (p 0)
  let e := sixVertexOneSectorEquiv N
  have heval (y : SixVertexSector N 1) :
      e y = sixVertexSectorPosition y 0 := rfl
  have hperiodic : z ^ N = 1 := sixVertexMultiplicativeBethe_one_periodic p hp
  have hsum0 : ∑ i : Fin N, z ^ i.val = 0 :=
    sum_sixVertexBethePhase_pow_eq_zero hphase hperiodic
  unfold SixVertexCoordinateBetheEigenrelation
  funext x
  rw [sixVertexSectorTransferComplex_mulVec_apply]
  have hreindex :
      (∑ y, (sixVertexSectorTransfer N 1 c x y : ℂ) *
          sixVertexCoordinateBetheWave c p y) =
        ∑ i : Fin N,
          (if e x = i then (2 : ℂ) else (c : ℂ) ^ 2) * z ^ i.val := by
    apply Fintype.sum_equiv e
    intro y
    rw [sixVertexSectorTransfer_one_apply,
      sixVertexCoordinateBetheWave_one]
    by_cases hxy : x = y
    · subst y
      simp [heval, z]
    · have hpos : sixVertexSectorPosition x 0 ≠
          sixVertexSectorPosition y 0 := by
        intro h
        apply hxy
        apply e.injective
        simpa [heval] using h
      simp [hxy, hpos, heval, z]
  rw [hreindex]
  have hsplit :
      (∑ i : Fin N,
          (if e x = i then (2 : ℂ) else (c : ℂ) ^ 2) * z ^ i.val) =
        (2 - (c : ℂ) ^ 2) * z ^ (e x).val +
          (c : ℂ) ^ 2 * ∑ i : Fin N, z ^ i.val := by
    calc
      _ = ∑ i : Fin N,
          ((2 - (c : ℂ) ^ 2) *
              (if e x = i then z ^ i.val else 0) +
            (c : ℂ) ^ 2 * z ^ i.val) := by
              apply Finset.sum_congr rfl
              intro i _
              by_cases hi : e x = i
              · simp [hi]
                ring
              · simp [hi]
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        simp
  rw [hsplit, hsum0, mul_zero, add_zero,
    sixVertexBetheEigenvalueCandidate_one p hphase]
  rw [Pi.smul_apply, sixVertexCoordinateBetheWave_one, heval]
  rfl



theorem sixVertexCoordinateBetheEigenrelation_one_of_nonzero
    {N : ℕ} (c : ℝ) (p : Fin 1 → ℝ)
    (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N 1 p)
    (hmem : p 0 ∈ Set.Ioo (-Real.pi) Real.pi) (hp0 : p 0 ≠ 0) :
    SixVertexCoordinateBetheEigenrelation (N := N) c p :=
  sixVertexCoordinateBetheEigenrelation_one c p hp
    (sixVertexBethePhase_ne_one_of_mem_Ioo hmem hp0)

end

end StatMech.FrontierD
