/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Rational power identities from exact integer Norton u certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- The exact rational physical matrix of Norton u, in column convention. -/
def monsterNortonUMatrixQ : Matrix (Fin 24) (Fin 24) ℚ :=
  (1 / 4 : ℚ) • monsterNortonUNumerator1.map (Int.castRingHom ℚ)

private theorem quarter_mul (A B C : Matrix (Fin 24) (Fin 24) ℤ)
    (h : A * B = (4 : ℤ) • C) :
    ((1/4 : ℚ) • A.map (Int.castRingHom ℚ)) *
      ((1/4 : ℚ) • B.map (Int.castRingHom ℚ)) =
      (1/4 : ℚ) • C.map (Int.castRingHom ℚ) := by
  rw [smul_mul_assoc, mul_smul_comm, ← Matrix.map_mul, h]
  ext i j
  change (1/4 : ℚ) * ((1/4 : ℚ) * ((4 : ℤ) * C i j : ℤ)) =
    (1/4 : ℚ) * (C i j : ℚ)
  push_cast
  ring

/-- The second power is the checked second numerator divided by four. -/
theorem monsterNortonUMatrixQ_two : monsterNortonUMatrixQ ^ 2 =
    (1/4 : ℚ) • monsterNortonUNumerator2.map (Int.castRingHom ℚ) := by
  rw [pow_two]
  exact quarter_mul _ _ _ monsterNortonU_numerator_1_1

/-- The fourth power is the checked fourth numerator divided by four. -/
theorem monsterNortonUMatrixQ_four : monsterNortonUMatrixQ ^ 4 =
    (1/4 : ℚ) • monsterNortonUNumerator4.map (Int.castRingHom ℚ) := by
  calc
    _ = monsterNortonUMatrixQ ^ 2 * monsterNortonUMatrixQ ^ 2 := by noncomm_ring
    _ = _ := by
      rw [monsterNortonUMatrixQ_two]
      exact quarter_mul _ _ _ monsterNortonU_numerator_2_2

/-- The eighth power is the checked eighth numerator divided by four. -/
theorem monsterNortonUMatrixQ_eight : monsterNortonUMatrixQ ^ 8 =
    (1/4 : ℚ) • monsterNortonUNumerator8.map (Int.castRingHom ℚ) := by
  calc
    _ = monsterNortonUMatrixQ ^ 4 * monsterNortonUMatrixQ ^ 4 := by noncomm_ring
    _ = _ := by
      rw [monsterNortonUMatrixQ_four]
      exact quarter_mul _ _ _ monsterNortonU_numerator_4_4

/-- The twelfth power is the checked twelfth numerator divided by four. -/
theorem monsterNortonUMatrixQ_twelve : monsterNortonUMatrixQ ^ 12 =
    (1/4 : ℚ) • monsterNortonUNumerator12.map (Int.castRingHom ℚ) := by
  calc
    _ = monsterNortonUMatrixQ ^ 8 * monsterNortonUMatrixQ ^ 4 := by noncomm_ring
    _ = _ := by
      rw [monsterNortonUMatrixQ_eight, monsterNortonUMatrixQ_four]
      exact quarter_mul _ _ _ monsterNortonU_numerator_8_4

/-- The concrete rational matrix has thirteenth power equal to the identity. -/
theorem monsterNortonUMatrixQ_thirteen : monsterNortonUMatrixQ ^ 13 = 1 := by
  calc
    _ = monsterNortonUMatrixQ ^ 12 * monsterNortonUMatrixQ := by noncomm_ring
    _ = _ := by
      rw [monsterNortonUMatrixQ_twelve]
      unfold monsterNortonUMatrixQ
      rw [smul_mul_assoc, mul_smul_comm, ← Matrix.map_mul,
        monsterNortonU_numerator_12_1]
      ext i j
      change (1/4 : ℚ) * ((1/4 : ℚ) * ((16 : ℤ) *
        (1 : Matrix (Fin 24) (Fin 24) ℤ) i j : ℤ)) =
        (1 : Matrix (Fin 24) (Fin 24) ℚ) i j
      by_cases h : i = j
      · subst j
        norm_num [Matrix.one_apply]
      · simp [h]

private theorem source_row (x : Fin 24 → ℝ) (i : Fin 24) :
    monsterNortonUFiber.val.2.val x i =
      qSign (golayEncoder (golayLabelCoefficients 82) i) *
        ∑ k : Fin 24, co1XiMatrix (omegaOrbitPermForward 0 i) k *
          ∑ j : Fin 24, co1XiMatrix (omegaOrbitPermForward 1 k) j * x j := by
  rw [monsterNortonUFiber_leech]
  rfl

private theorem sign_entry (i : Fin 24) :
    (monsterSourceY82Physical i i : ℝ) =
      qSign (golayEncoder (golayLabelCoefficients 82) i) := by
  simp [monsterSourceY82Physical, monsterSourceY82Code, qSign]

private theorem matrix_entry (i j : Fin 24) :
    monsterNortonUMatrixQ.map (Rat.castHom ℝ) i j =
      qSign (golayEncoder (golayLabelCoefficients 82) i) *
        ∑ k : Fin 24, co1XiMatrix (omegaOrbitPermForward 0 i) k *
          co1XiMatrix (omegaOrbitPermForward 1 k) j := by
  change (((1/4 : ℚ) * (monsterNortonUNumerator1 i j : ℚ) : ℚ) : ℝ) = _
  rw [monsterNortonU_numerator_source]
  push_cast
  change (1/4 : ℝ) * ((monsterSourceY82Physical i i : ℝ) *
      ∑ k : Fin 24, (co1XiNumerator (omegaOrbitPermForward 0 i) k : ℝ) *
        (co1XiNumerator (omegaOrbitPermForward 1 k) j : ℝ)) =
    qSign (golayEncoder (golayLabelCoefficients 82) i) *
      ∑ k : Fin 24, (((co1XiNumerator (omegaOrbitPermForward 0 i) k : ℚ) / 2 : ℚ) : ℝ) *
        (((co1XiNumerator (omegaOrbitPermForward 1 k) j : ℚ) / 2 : ℚ) : ℝ)
  push_cast
  rw [sign_entry]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The exact matrix is the actual lattice action of the literal seven-factor word. -/
theorem monsterNortonUFiber_leech_matrix (x : Fin 24 → ℝ) :
    monsterNortonUFiber.val.2.val x =
      monsterNortonUMatrixQ.map (Rat.castHom ℝ) *ᵥ x := by
  ext i
  rw [source_row]
  change _ = ∑ j : Fin 24, monsterNortonUMatrixQ.map (Rat.castHom ℝ) i j * x j
  simp only [matrix_entry, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
