/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring

/-! # Nathanson’s construction of a sum-dominated set -/

namespace MetaMathlibExt

@[expose] public section

open scoped Pointwise

/-- **Nathanson's sum-dominated set.** For a set $S$ of integers write
$S + S = \{s + s' : s, s' \in S\}$ and $S - S = \{s - s' : s, s' \in S\}$. Let $m$, $d$, $k$ be
integers with $m \ge 4$, $1 \le d \le m - 1$ and $2d \ne m$, and suppose $k \ge 3$ if $2d < m$
and $k \ge 4$ if $2d > m$. Let $B = \{0, 1, \dots, m - 1\} \setminus \{d\}$,
$L = \{jm - d : 1 \le j \le k\}$, $A^* = B \cup L \cup \{(k + 1)m - 2d - b : b \in B\}$ and
$A = A^* \cup \{m\}$. Then $|A - A| < |A + A|$, $2m \in A + A$, $2m \notin A^* + A^*$, and
$\{a - m : a \in A^*\} \subseteq A^* - A^*$.

Source: Yorick Herrmann, Connor Hill, Merlin Phillips, Daniel Flores, Steven J. Miller and
Steven Senger, *Additional Constructions of Sequences of Alternating Sum and Difference
Dominated Sets*, INTEGERS 26 (2026), Article A88, Theorem 2 (`integers-2026-A88-thm-2`). -/
public theorem nathanson_mstd_construction {m d k : ℤ} (hm : 4 ≤ m) (hd : 1 ≤ d)
    (hdm : d ≤ m - 1) (hd2 : 2 * d ≠ m) (hk3 : 2 * d < m → 3 ≤ k) (hk4 : m < 2 * d → 4 ≤ k) :
    let B := (Finset.Icc 0 (m - 1)).erase d
    let As := B ∪ (Finset.Icc 1 k).image (fun j => j * m - d) ∪
      B.image (fun b => (k + 1) * m - 2 * d - b)
    let A := insert m As
    (A - A).card < (A + A).card ∧ 2 * m ∈ A + A ∧ 2 * m ∉ As + As ∧ As - {m} ⊆ As - As := by
  let c : ℤ := (k + 1) * m - 2 * d
  let B := (Finset.Icc 0 (m - 1)).erase d
  let L := (Finset.Icc 1 k).image fun j => j * m - d
  let S := B ∪ L ∪ B.image (fun b => c - b)
  let A := insert m S
  change (A - A).card < (A + A).card ∧ 2 * m ∈ A + A ∧ 2 * m ∉ S + S ∧ S - {m} ⊆ S - S
  have hm0 : 0 < m := by omega
  have hk : 3 ≤ k := by
    by_cases h : 2 * d < m
    · exact hk3 h
    · have h' := hk4 (by omega)
      omega
  have hB (b : ℤ) : b ∈ B ↔ b ≠ d ∧ 0 ≤ b ∧ b ≤ m - 1 := by
    simp only [B, Finset.mem_erase, Finset.mem_Icc]
  have hS (a : ℤ) : a ∈ S ↔ a ∈ B ∨ (∃ j : ℤ, 1 ≤ j ∧ j ≤ k ∧ j * m - d = a) ∨
      ∃ b ∈ B, c - b = a := by
    simp only [S, L, Finset.mem_union, Finset.mem_image, Finset.mem_Icc, or_assoc, and_assoc]
  have hBS : B ⊆ S := fun b hb => (hS b).mpr (Or.inl hb)
  have hL (j : ℤ) (hj : 1 ≤ j) (hjk : j ≤ k) : j * m - d ∈ S :=
    (hS _).mpr (Or.inr (Or.inl ⟨j, hj, hjk, rfl⟩))
  have h0 : 0 ∈ S := hBS ((hB 0).mpr (by omega))
  have hreflect (a : ℤ) (ha : a ∈ S) : c - a ∈ S := by
    rcases (hS a).mp ha with hb | ⟨j, hj, hjk, rfl⟩ | ⟨b, hb, rfl⟩
    · exact (hS _).mpr (Or.inr (Or.inr ⟨a, hb, rfl⟩))
    · have he : c - (j * m - d) = (k + 1 - j) * m - d := by
        dsimp only [c]
        ring
      rw [he]
      exact hL (k + 1 - j) (by omega) (by omega)
    · rw [show c - (c - b) = b by omega]
      exact hBS hb
  -- Small differences are available even when the erased point is at the right endpoint.
  have hsmall (z : ℤ) (hz0 : 0 ≤ z) (hzm : z ≤ m) : z ∈ S - S := by
    by_cases hzm' : z = m
    · subst z
      exact Finset.mem_sub.mpr ⟨2 * m - d, hL 2 (by omega) (by omega),
        1 * m - d, hL 1 (by omega) (by omega), by omega⟩
    by_cases hzd : z = d
    · subst z
      by_cases hdend : d = m - 1
      · exact Finset.mem_sub.mpr ⟨2 * m - d, hL 2 (by omega) (by omega),
          2, hBS ((hB 2).mpr (by omega)), by omega⟩
      by_cases hd1 : d = 1
      · exact Finset.mem_sub.mpr ⟨3, hBS ((hB 3).mpr (by omega)),
          2, hBS ((hB 2).mpr (by omega)), by omega⟩
      · exact Finset.mem_sub.mpr ⟨d + 1, hBS ((hB _).mpr (by omega)),
          1, hBS ((hB 1).mpr (by omega)), by omega⟩
    · exact Finset.mem_sub.mpr ⟨z, hBS ((hB z).mpr (by omega)), 0, h0, sub_zero z⟩
  have hneg (z : ℤ) (hz : z ∈ S - S) : -z ∈ S - S := by
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hz
    exact Finset.mem_sub.mpr ⟨v, hv, u, hu, by omega⟩
  have hBsum (b : ℤ) (hb : b ∈ B) : m + b ∈ S + S := by
    have hbb := (hB b).mp hb
    by_cases hb0 : b = 0
    · by_cases hend : d = 1 ∨ d = m - 1
      · exact Finset.mem_add.mpr ⟨2, hBS ((hB 2).mpr (by omega)),
          m - 2, hBS ((hB _).mpr (by omega)), by omega⟩
      · exact Finset.mem_add.mpr ⟨1, hBS ((hB 1).mpr (by omega)),
          m - 1, hBS ((hB _).mpr (by omega)), by omega⟩
    · by_cases hlow : b + d < m
      · exact Finset.mem_add.mpr ⟨1 * m - d, hL 1 (by omega) (by omega),
          b + d, hBS ((hB _).mpr (by omega)), by omega⟩
      · exact Finset.mem_add.mpr ⟨2 * m - d, hL 2 (by omega) (by omega),
          b + d - m, hBS ((hB _).mpr (by omega)), by omega⟩
  have hmixed (a : ℤ) (ha : a ∈ S) : a - m ∈ S - S := by
    rcases (hS a).mp ha with hb | ⟨j, hj, hjk, rfl⟩ | ⟨b, hb, rfl⟩
    · have hbb := (hB a).mp hb
      rw [show a - m = -(m - a) by omega]
      exact hneg _ (hsmall (m - a) (by omega) (by omega))
    · by_cases h : j = 1
      · subst j
        rw [show (1 : ℤ) * m - d - m = -d by omega]
        exact hneg _ (hsmall d (by omega) (by omega))
      · exact Finset.mem_sub.mpr ⟨(j - 1) * m - d, hL (j - 1) (by omega) (by omega),
          0, h0, by ring⟩
    · obtain ⟨u, hu, v, hv, he⟩ := Finset.mem_add.mp (hBsum b hb)
      exact Finset.mem_sub.mpr ⟨c - u, hreflect u hu, v, hv, by omega⟩
  -- The reflected block lies above 2m; only the first two blocks can contribute to 2m.
  have hCgt (b : ℤ) (hb : b ∈ B) : 2 * m < c - b := by
    have hbb := (hB b).mp hb
    change 2 * m < (k + 1) * m - 2 * d - b
    rw [add_mul, one_mul]
    by_cases h : 2 * d < m
    · have hmul := Int.mul_le_mul_of_nonneg_right (hk3 h) hm0.le
      omega
    · have hk' := hk4 (by omega)
      have hmul := Int.mul_le_mul_of_nonneg_right hk' hm0.le
      omega
  have hnonneg (a : ℤ) (ha : a ∈ S) : 0 ≤ a := by
    rcases (hS a).mp ha with hb | ⟨j, hj, _, rfl⟩ | ⟨b, hb, rfl⟩
    · exact ((hB a).mp hb).2.1
    · have hmul := Int.mul_le_mul_of_nonneg_right hj hm0.le
      omega
    · have he := hCgt b hb
      omega
  have hbelow (a : ℤ) (ha : a ∈ S) (hle : a ≤ 2 * m) :
      a ∈ B ∨ ∃ j : ℤ, 1 ≤ j ∧ j ≤ k ∧ j * m - d = a := by
    rcases (hS a).mp ha with hb | hl | ⟨b, hb, rfl⟩
    · exact Or.inl hb
    · exact Or.inr hl
    · exact (not_lt_of_ge hle (hCgt b hb)).elim
  have hBL (b j : ℤ) (hb : b ∈ B) (hj : 1 ≤ j) : b + (j * m - d) ≠ 2 * m := by
    have hbb := (hB b).mp hb
    intro he
    by_cases hj1 : j = 1
    · subst j
      omega
    by_cases hj2 : j = 2
    · subst j
      omega
    · have hmul := Int.mul_le_mul_of_nonneg_right (show 3 ≤ j by omega) hm0.le
      omega
  have hLL (i j : ℤ) : (i * m - d) + (j * m - d) ≠ 2 * m := by
    intro heq
    have he : (i + j - 2) * m = 2 * d := calc
      _ = (i * m - d) + (j * m - d) - 2 * m + 2 * d := by ring
      _ = 2 * d := by omega
    have hpos : 0 < i + j - 2 := by
      by_contra! hh
      have hmul := Int.mul_nonpos_of_nonpos_of_nonneg hh hm0.le
      omega
    have hlt : i + j - 2 < 2 := by
      by_contra! hh
      have hmul := Int.mul_le_mul_of_nonneg_right hh hm0.le
      omega
    rw [show i + j - 2 = 1 by omega, one_mul] at he
    exact hd2 he.symm
  have hnone : 2 * m ∉ S + S := by
    intro hz
    obtain ⟨a, ha, b, hb, he⟩ := Finset.mem_add.mp hz
    have hla : a ≤ 2 * m := by have hn := hnonneg b hb; omega
    have hlb : b ≤ 2 * m := by have hn := hnonneg a ha; omega
    rcases hbelow a ha hla with haB | ⟨i, hi, _, rfl⟩
    · rcases hbelow b hb hlb with hbB | ⟨j, hj, _, rfl⟩
      · have ha' := (hB a).mp haB
        have hb' := (hB b).mp hbB
        omega
      · exact hBL a j haB hj he
    · rcases hbelow b hb hlb with hbB | ⟨j, _, _, rfl⟩
      · exact hBL b i hbB hi (by omega)
      · exact hLL i j he
  have hSA : S ⊆ A := fun a ha => Finset.mem_insert.mpr (Or.inr ha)
  have hmA : m ∈ A := Finset.mem_insert.mpr (Or.inl rfl)
  have hnew : 2 * m ∈ A + A := Finset.mem_add.mpr ⟨m, hmA, m, hmA, by omega⟩
  have hkeep : A - A ⊆ S - S := by
    intro z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
    rcases Finset.mem_insert.mp ha with ham | ha'
    · subst a
      rcases Finset.mem_insert.mp hb with hbm | hb'
      · subst b
        simpa only [sub_self] using hsmall 0 (by omega) (by omega)
      · rw [show m - b = -(b - m) by omega]
        exact hneg _ (hmixed b hb')
    · rcases Finset.mem_insert.mp hb with hbm | hb'
      · subst b
        exact hmixed a ha'
      · exact Finset.sub_mem_sub ha' hb'
  have hclosed : (S - S).card ≤ (S + S).card := by
    apply Finset.card_le_card_of_injOn (fun z : ℤ => c + z)
    · intro z hz
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp (Finset.mem_coe.mp hz)
      change c + (u - v) ∈ S + S
      exact Finset.mem_add.mpr ⟨u, hu, c - v, hreflect v hv, by omega⟩
    · intro u _ v _ huv
      exact add_left_cancel huv
  have hslt : S + S ⊂ A + A :=
    (Finset.ssubset_iff_of_subset (Finset.add_subset_add hSA hSA)).mpr ⟨2 * m, hnew, hnone⟩
  refine ⟨(Finset.card_le_card hkeep).trans_lt (hclosed.trans_lt (Finset.card_lt_card hslt)),
    hnew, hnone, ?_⟩
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
  rw [Finset.mem_singleton.mp hb]
  exact hmixed a ha

end

end MetaMathlibExt
