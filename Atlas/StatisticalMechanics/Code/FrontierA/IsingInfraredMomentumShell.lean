/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingInfraredContinuumGreen
import Code.Lattice.BoxSurfaceVolume

open Finset Set
open scoped BigOperators

namespace StatMech.FrontierA

open Lattice


noncomputable def integerMomentumNormSq {d : Nat} (m : Site d) : Real :=
  ∑ i : Fin d, (m i : Real) ^ 2

theorem integerMomentumNormSq_nonneg {d : Nat} (m : Site d) :
    0 ≤ integerMomentumNormSq m := by
  unfold integerMomentumNormSq
  positivity

theorem integerMomentumNormSq_pos {d : Nat} {m : Site d} (hm : m ≠ 0) :
    0 < integerMomentumNormSq m := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    apply hm
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  unfold integerMomentumNormSq
  exact Finset.sum_pos' (fun j _ ↦ sq_nonneg (m j : Real))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero (by exact_mod_cast hi)⟩


theorem natCast_sq_le_integerMomentumNormSq_of_mem_shell
    {d r : Nat} {m : Site d} (hr : 1 ≤ r) (hm : m ∈ boxSV_vbF d r) :
    (r : Real) ^ 2 ≤ integerMomentumNormSq m := by
  have hm' : m ∈ vertexBoundary d r := by
    rw [← boxSV_coe_vbF d r]
    exact hm
  rw [mem_vertexBoundary] at hm'
  rw [mem_box] at hm'
  obtain ⟨i, hiInner⟩ := not_forall.mp hm'.2
  have hiOuter := hm'.1 i
  have hi : (m i).natAbs = r := by omega
  have hiSq : (r : Real) ^ 2 = (m i : Real) ^ 2 := by
    have hiReal : |(m i : Real)| = (r : Real) := by
      calc
        |(m i : Real)| = ((|m i| : Int) : Real) := Int.cast_abs.symm
        _ = (((m i).natAbs : Int) : Real) := by
          rw [Int.natCast_natAbs]
        _ = (r : Real) := by norm_cast
    nlinarith [sq_abs (m i : Real)]
  rw [hiSq, integerMomentumNormSq]
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (m j : Real))
    (Finset.mem_univ i)



theorem sum_inv_integerMomentumNormSq_shell_le
    (d r : Nat) (hr : 1 ≤ r) :
    ∑ m ∈ boxSV_vbF d r, (integerMomentumNormSq m)⁻¹ ≤
      ((boxSV_vbF d r).card : Real) / (r : Real) ^ 2 := by
  have hrPos : (0 : Real) < (r : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  calc
    ∑ m ∈ boxSV_vbF d r, (integerMomentumNormSq m)⁻¹ ≤
        ∑ _m ∈ boxSV_vbF d r, ((r : Real) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro m hm
      exact inv_anti₀ (sq_pos_of_pos hrPos)
        (natCast_sq_le_integerMomentumNormSq_of_mem_shell hr hm)
    _ = ((boxSV_vbF d r).card : Real) / (r : Real) ^ 2 := by
      simp [div_eq_mul_inv]

theorem integerMomentumShell_card_le (d r : Nat) (hr : 1 ≤ r) :
    ((boxSV_vbF d r).card : Real) ≤
      2 * d * (2 * (r : Real) + 1) ^ (d - 1) := by
  have hcard : (boxSV_vbF d r).card = boxSV_boundaryCard d r := by
    rw [boxSV_vbF_eq_toFinset]
    rfl
  rw [hcard, boxSV_boundary_card d r hr]
  have hle : (2 * r - 1) ^ d ≤ (2 * r + 1) ^ d :=
    Nat.pow_le_pow_left (by omega) d
  rw [Nat.cast_sub hle]
  have hrR : (1 : Real) ≤ r := by exact_mod_cast hr
  have hpow := boxSV_pow_sub_pow_le
    (2 * (r : Real) + 1) (2 * (r : Real) - 1)
    (by linarith) (by linarith) d
  have hminus : ((2 * r - 1 : Nat) : Real) = 2 * (r : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * r)]
    push_cast
    ring
  push_cast
  rw [hminus]
  calc
    (2 * (r : Real) + 1) ^ d - (2 * (r : Real) - 1) ^ d ≤
        ((2 * (r : Real) + 1) - (2 * (r : Real) - 1)) *
          (d * (2 * (r : Real) + 1) ^ (d - 1)) := hpow
    _ = 2 * d * (2 * (r : Real) + 1) ^ (d - 1) := by ring


theorem sum_inv_integerMomentumNormSq_shell_le_power
    (d r : Nat) (hd : 3 ≤ d) (hr : 1 ≤ r) :
    ∑ m ∈ boxSV_vbF d r, (integerMomentumNormSq m)⁻¹ ≤
      2 * d * 3 ^ (d - 1) * (r : Real) ^ (d - 3) := by
  have hrPos : (0 : Real) < (r : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hcard := integerMomentumShell_card_le d r hr
  have hthree : 2 * (r : Real) + 1 ≤ 3 * r := by
    have : (1 : Real) ≤ r := by exact_mod_cast hr
    linarith
  have hpow : (2 * (r : Real) + 1) ^ (d - 1) ≤
      (3 * (r : Real)) ^ (d - 1) := by
    exact pow_le_pow_left₀ (by positivity) hthree _
  calc
    ∑ m ∈ boxSV_vbF d r, (integerMomentumNormSq m)⁻¹ ≤
        ((boxSV_vbF d r).card : Real) / (r : Real) ^ 2 :=
      sum_inv_integerMomentumNormSq_shell_le d r hr
    _ ≤ (2 * d * (2 * (r : Real) + 1) ^ (d - 1)) /
        (r : Real) ^ 2 := by
      exact div_le_div_of_nonneg_right hcard (sq_nonneg (r : Real))
    _ ≤ (2 * d * (3 * (r : Real)) ^ (d - 1)) /
        (r : Real) ^ 2 := by
      gcongr
    _ = 2 * d * 3 ^ (d - 1) * (r : Real) ^ (d - 3) := by
      rw [mul_pow]
      field_simp
      ring_nf
      rw [← pow_add]
      congr 2
      omega


noncomputable def integerMomentumBoxWithoutZero (d M : Nat) :
    Finset (Site d) :=
  boxSV_boxF d M \ {0}

theorem integerMomentumBoxWithoutZero_succ (d M : Nat) :
    integerMomentumBoxWithoutZero d (M + 1) =
      integerMomentumBoxWithoutZero d M ∪ boxSV_vbF d (M + 1) := by
  classical
  ext m
  simp only [integerMomentumBoxWithoutZero, Finset.mem_sdiff,
    Finset.mem_singleton, Finset.mem_union, boxSV_vbF]
  constructor
  · rintro ⟨hmOuter, hm0⟩
    by_cases hmInner : m ∈ boxSV_boxF d M
    · exact Or.inl ⟨hmInner, hm0⟩
    · exact Or.inr ⟨by simpa only [Nat.add_sub_cancel] using hmOuter,
        by simpa only [Nat.add_sub_cancel] using hmInner⟩
  · rintro (⟨hmInner, hm0⟩ | ⟨hmOuter, hmNotInner⟩)
    · refine ⟨boxSV_boxF_subset d (Nat.le_succ M) hmInner, hm0⟩
    · refine ⟨hmOuter, ?_⟩
      intro hm0
      subst m
      apply hmNotInner
      rw [boxSV_mem_boxF]
      intro i
      simp

theorem disjoint_integerMomentumBoxWithoutZero_shell_succ (d M : Nat) :
    Disjoint (integerMomentumBoxWithoutZero d M) (boxSV_vbF d (M + 1)) := by
  classical
  rw [Finset.disjoint_left]
  intro m hmBox hmShell
  rw [integerMomentumBoxWithoutZero, Finset.mem_sdiff] at hmBox
  rw [boxSV_vbF, Finset.mem_sdiff] at hmShell
  exact hmShell.2 (by simpa only [Nat.add_sub_cancel] using hmBox.1)



theorem sum_inv_integerMomentumNormSq_box_eq_sum_shells (d M : Nat) :
    ∑ m ∈ integerMomentumBoxWithoutZero d M,
        (integerMomentumNormSq m)⁻¹ =
      ∑ r ∈ Finset.range M,
        ∑ m ∈ boxSV_vbF d (r + 1),
          (integerMomentumNormSq m)⁻¹ := by
  induction M with
  | zero =>
      have hzero : integerMomentumBoxWithoutZero d 0 = ∅ := by
        classical
        ext m
        simp only [integerMomentumBoxWithoutZero, Finset.mem_sdiff,
          Finset.mem_singleton, Finset.notMem_empty, iff_false]
        intro hm
        apply hm.2
        funext i
        have hi := (boxSV_mem_boxF.mp hm.1) i
        simp only [Finset.mem_Icc] at hi
        change m i = 0
        omega
      simp [hzero]
  | succ M ih =>
      rw [integerMomentumBoxWithoutZero_succ,
        Finset.sum_union (disjoint_integerMomentumBoxWithoutZero_shell_succ d M),
        ih, Finset.sum_range_succ]



theorem sum_inv_integerMomentumNormSq_box_le_power
    (d M : Nat) (hd : 3 ≤ d) :
    ∑ m ∈ integerMomentumBoxWithoutZero d M,
        (integerMomentumNormSq m)⁻¹ ≤
      2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 2) := by
  rw [sum_inv_integerMomentumNormSq_box_eq_sum_shells]
  by_cases hM : M = 0
  · subst M
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM
  have hterm (r : Nat) (hr : r ∈ Finset.range M) :
      ∑ m ∈ boxSV_vbF d (r + 1),
          (integerMomentumNormSq m)⁻¹ ≤
        2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 3) := by
    calc
      ∑ m ∈ boxSV_vbF d (r + 1),
          (integerMomentumNormSq m)⁻¹ ≤
          2 * d * 3 ^ (d - 1) * ((r + 1 : Nat) : Real) ^ (d - 3) :=
        sum_inv_integerMomentumNormSq_shell_le_power d (r + 1) hd (by omega)
      _ ≤ 2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 3) := by
        gcongr
        exact_mod_cast (Finset.mem_range.mp hr)
  calc
    ∑ r ∈ Finset.range M,
        ∑ m ∈ boxSV_vbF d (r + 1),
          (integerMomentumNormSq m)⁻¹ ≤
        ∑ _r ∈ Finset.range M,
          2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 3) := by
      exact Finset.sum_le_sum hterm
    _ = 2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 2) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      calc
        (M : Real) *
            (2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 3)) =
            2 * d * 3 ^ (d - 1) *
              ((M : Real) * (M : Real) ^ (d - 3)) := by ring
        _ = 2 * d * 3 ^ (d - 1) * (M : Real) ^ (d - 2) := by
          rw [← pow_succ']
          congr 3
          omega

end StatMech.FrontierA
