/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Combinatorics.Additive.ChuMSTDFamilies
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

@[expose] public section

open Pointwise

private theorem period_index_eq (P x y : ℤ) (j j' : ℕ)
    (hx : 12 ≤ x ∧ x ≤ P + 8) (hy : 12 ≤ y ∧ y ≤ P + 8)
    (h : P * j + x = P * j' + y) : j = j' := by
  have hP : 0 < P := by omega
  rcases lt_trichotomy j j' with hj | hj | hj
  · have hjz : (j : ℤ) + 1 ≤ j' := by exact_mod_cast hj
    nlinarith
  · exact hj
  · have hjz : (j' : ℤ) + 1 ≤ j := by exact_mod_cast hj
    nlinarith

private theorem step_ne (s : ℤ) (hs : 8 ≤ s) (i j : ℕ) :
    s * i + 4 ≠ s * j + 8 := by
  intro h
  by_cases hij : i ≤ j
  · have hij' : (i : ℤ) ≤ j := by exact_mod_cast hij
    nlinarith
  · have hij' : (j : ℤ) + 1 ≤ i := by omega
    nlinarith

private theorem offsets_ne (s B : ℤ) (hs : 8 ≤ s) (i i' : ℕ)
    (hi : s ≤ s * i ∧ s * i ≤ B) (hi' : s ≤ s * i' ∧ s * i' ≤ B)
    (a b : Fin 6) (hab : a ≠ b) :
    ![s * i + 4, s * i + 8, B + 12, B + s * i + 8, B + s * i + 12, 2 * B + 16] a ≠
      ![s * i' + 4, s * i' + 8, B + 12, B + s * i' + 8, B + s * i' + 12, 2 * B + 16] b := by
  intro heq
  have hgap := step_ne s hs i i'
  have hgap' := step_ne s hs i' i
  fin_cases a <;> fin_cases b <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ'] at heq hab <;>
    omega

private theorem six_disjoint (s : ℤ) (l t : ℕ) (hs : 8 ≤ s) (hl : 0 < l) :
    let B := s * l
    let P := 2 * B + 8
    let X₁ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + s * p.1 + 4
    let X₂ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + s * p.1 + 8
    let X₃ := (Finset.range t).image fun j : ℕ => P * j + B + 12
    let X₄ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + B + s * p.1 + 8
    let X₅ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + B + s * p.1 + 12
    let X₆ := (Finset.range t).image fun j : ℕ => P * j + 2 * B + 16
    Pairwise fun a b : Fin 6 =>
      Disjoint (![X₁, X₂, X₃, X₄, X₅, X₆] a) (![X₁, X₂, X₃, X₄, X₅, X₆] b) := by
  intro B P X₁ X₂ X₃ X₄ X₅ X₆
  let F := ![X₁, X₂, X₃, X₄, X₅, X₆]
  let O (a : Fin 6) (i : ℕ) : ℤ :=
    ![s * i + 4, s * i + 8, B + 12, B + s * i + 8, B + s * i + 12, 2 * B + 16] a
  have hmem (a : Fin 6) (z : ℤ) (hz : z ∈ F a) :
      ∃ i j : ℕ, 1 ≤ i ∧ i ≤ l ∧ j < t ∧ P * j + O a i = z := by
    fin_cases a <;>
      simp only [F, X₁, X₂, X₃, X₄, X₅, X₆, Matrix.cons_val_zero',
        Matrix.cons_val_succ', Finset.mem_image] at hz
    · obtain ⟨⟨i, j⟩, hij, hz⟩ := hz
      simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hij
      exact ⟨i, j, hij.1.1, hij.1.2, hij.2, by simpa [O, add_assoc] using hz⟩
    · obtain ⟨⟨i, j⟩, hij, hz⟩ := hz
      simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hij
      exact ⟨i, j, hij.1.1, hij.1.2, hij.2, by simpa [O, add_assoc] using hz⟩
    · obtain ⟨j, hj, hz⟩ := hz
      exact ⟨1, j, le_rfl, hl, Finset.mem_range.mp hj, by simpa [O, add_assoc] using hz⟩
    · obtain ⟨⟨i, j⟩, hij, hz⟩ := hz
      simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hij
      exact ⟨i, j, hij.1.1, hij.1.2, hij.2, by simpa [O, add_assoc] using hz⟩
    · obtain ⟨⟨i, j⟩, hij, hz⟩ := hz
      simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hij
      exact ⟨i, j, hij.1.1, hij.1.2, hij.2, by simpa [O, add_assoc] using hz⟩
    · obtain ⟨j, hj, hz⟩ := hz
      exact ⟨1, j, le_rfl, hl, Finset.mem_range.mp hj, by simpa [O, add_assoc] using hz⟩
  have hb (i : ℕ) (hi : 1 ≤ i) (hil : i ≤ l) : s ≤ s * i ∧ s * i ≤ B := by
    have hi' : (1 : ℤ) ≤ i := by exact_mod_cast hi
    have hil' : (i : ℤ) ≤ l := by exact_mod_cast hil
    dsimp only [B]
    constructor <;> nlinarith
  have hoff (a : Fin 6) (i : ℕ) (hi : 1 ≤ i) (hil : i ≤ l) :
      12 ≤ O a i ∧ O a i ≤ P + 8 := by
    have hbi := hb i hi hil
    fin_cases a <;> simp only [O, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
      dsimp only [P] <;> constructor <;> nlinarith
  change Pairwise fun a b => Disjoint (F a) (F b)
  intro a b hab
  rw [Finset.disjoint_left]
  intro z hza hzb
  obtain ⟨i, j, hi, hil, hj, ha⟩ := hmem a z hza
  obtain ⟨i', j', hi', hil', hj', hb'⟩ := hmem b z hzb
  have hperiod := period_index_eq P (O a i) (O b i') j j'
    (hoff a i hi hil) (hoff b i' hi' hil') (ha.trans hb'.symm)
  subst j'
  have heq : O a i = O b i' := by linarith
  exact offsets_ne s B hs i i' (hb i hi hil) (hb i' hi' hil') a b hab heq

/-- **Six disjoint families in the sumset of the Chu family set.** Let $k$, $l$, $t$ be positive
integers, let $A \subseteq \mathbb{Z}$ be the Chu family set with parameters $k$, $l$, $t$, and
let $P = 8kl + 8l + 8$. Let $X_1$, $X_2$, $X_4$, $X_5$ be the sets of the integers
$Pj + (4k + 4)i + 4$, $Pj + (4k + 4)i + 8$, $Pj + 4kl + 4l + (4k + 4)i + 8$ and
$Pj + 4kl + 4l + (4k + 4)i + 12$ respectively, for $1 \le i \le l$ and $0 \le j \le t - 1$, and
let $X_3$, $X_6$ be the sets of the integers $Pj + 4kl + 4l + 12$ and $Pj + 8kl + 8l + 16$
respectively, for $0 \le j \le t - 1$. Then $A + A$ contains $\{0, 4, 8\}$ and each of
$X_1, \ldots, X_6$, and the sets $X_1, \ldots, X_6$ are pairwise disjoint.

Source: Manish Kumar, Mohan and Ram Krishna Pandey, *A Conjecture of Chu et al. and a New
Family of MSTD Sets*, INTEGERS 24 (2024), Article A32, Lemma 7 (`integers-2024-A32-lem-7`). -/
public theorem chuFamilyKLT_add_supset_six_families {k l t : ℕ} (hk : 0 < k) (hl : 0 < l)
    (ht : 0 < t) :
    let P : ℤ := 8 * k * l + 8 * l + 8
    let X₁ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + (4 * k + 4) * p.1 + 4
    let X₂ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + (4 * k + 4) * p.1 + 8
    let X₃ := (Finset.range t).image fun j : ℕ => P * j + (4 * k * l + 4 * l) + 12
    let X₄ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + (4 * k * l + 4 * l) + (4 * k + 4) * p.1 + 8
    let X₅ := (Finset.Icc 1 l ×ˢ Finset.range t).image fun p : ℕ × ℕ =>
      P * p.2 + (4 * k * l + 4 * l) + (4 * k + 4) * p.1 + 12
    let X₆ := (Finset.range t).image fun j : ℕ => P * j + (8 * k * l + 8 * l) + 16
    {0, 4, 8} ∪ X₁ ∪ X₂ ∪ X₃ ∪ X₄ ∪ X₅ ∪ X₆ ⊆ chuFamilyKLT k l t + chuFamilyKLT k l t ∧
      Pairwise fun a b : Fin 6 =>
        Disjoint (![X₁, X₂, X₃, X₄, X₅, X₆] a) (![X₁, X₂, X₃, X₄, X₅, X₆] b) := by
  intro P X₁ X₂ X₃ X₄ X₅ X₆
  let Q : ℤ := 4 * k * l + 4 * l + 4
  have hzero : (0 : ℤ) ∈ chuFamilyKLT k l t := by
    cases t <;> simp [chuFamilyKLT, List.replicate_succ, List.flatten_cons,
      List.append_assoc, setOfConsecutiveDifferences_cons]
  have hboundary (j : ℕ) (hj : j ≤ t) : Q * j ∈ chuFamilyKLT k l t := by
    cases j with
    | zero => simpa using hzero
    | succ j =>
      have h := chuFamilyKLT_mem_block_starts hk hl ht l j le_rfl (by omega)
      convert h using 1
      simp only [Nat.cast_add, Nat.cast_one]
      dsimp only [Q]
      ring
  have hfour (j : ℕ) (hj : j ≤ t) : Q * j + 4 ∈ chuFamilyKLT k l t := by
    by_cases h : j < t
    · have hm := chuFamilyKLT_mem_block_starts hk hl ht 0 j (by omega) h
      simpa [Q, add_comm] using hm
    · have hjt : j = t := by omega
      subst j
      have hm := (chuFamilyKLT_mem hk hl ht).2.2
      convert hm using 1
      push_cast
      dsimp only [Q]
      ring
  have hstart (i j : ℕ) (hi : i ≤ l) (hj : j < t) :
      Q * j + (4 * k + 4) * i + 4 ∈ chuFamilyKLT k l t := by
    simpa [Q, add_comm, add_left_comm, add_assoc] using
      chuFamilyKLT_mem_block_starts hk hl ht i j hi hj
  have hfour₀ : (4 : ℤ) ∈ chuFamilyKLT k l t := by simpa using hfour 0 (by omega)
  have hsum {a b z : ℤ} (ha : a ∈ chuFamilyKLT k l t)
      (hb : b ∈ chuFamilyKLT k l t) (h : a + b = z) :
      z ∈ chuFamilyKLT k l t + chuFamilyKLT k l t :=
    h ▸ Finset.add_mem_add ha hb
  constructor
  · intro z hz
    simp only [Finset.mem_union] at hz
    rcases hz with ((((((hz | hz) | hz) | hz) | hz) | hz) | hz)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hsum hzero hzero (by ring)
      · exact hsum hzero hfour₀ (by ring)
      · exact hsum hfour₀ hfour₀ (by ring)
    · obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hz
      simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hij
      exact hsum (hstart i j hij.1.2 hij.2) (hboundary j (by omega))
        (by dsimp only [P, Q]; ring)
    · obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hz
      simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hij
      exact hsum (hstart i j hij.1.2 hij.2) (hfour j (by omega))
        (by dsimp only [P, Q]; ring)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      have hjt := Finset.mem_range.mp hj
      exact hsum (hfour (j + 1) (by omega)) (hfour j (by omega))
        (by dsimp only [P, Q]; push_cast; ring)
    · obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hz
      simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hij
      exact hsum (hstart i j hij.1.2 hij.2) (hboundary (j + 1) (by omega))
        (by dsimp only [P, Q]; push_cast; ring)
    · obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hz
      simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hij
      exact hsum (hstart i j hij.1.2 hij.2) (hfour (j + 1) (by omega))
        (by dsimp only [P, Q]; push_cast; ring)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      have hjt := Finset.mem_range.mp hj
      exact hsum (hfour (j + 1) (by omega)) (hfour (j + 1) (by omega))
        (by dsimp only [P, Q]; push_cast; ring)
  · have hs : (8 : ℤ) ≤ 4 * k + 4 := by omega
    have hB : (4 * (k : ℤ) + 4) * l = 4 * k * l + 4 * l := by ring
    have hP : 2 * (4 * (k : ℤ) * l + 4 * l) + 8 = P := by dsimp only [P]; ring
    have hB₂ : 2 * (4 * (k : ℤ) * l + 4 * l) = 8 * k * l + 8 * l := by ring
    simpa only [hB, hP, hB₂, X₁, X₂, X₃, X₄, X₅, X₆] using six_disjoint (4 * k + 4) l t hs hl

end

end MetaMathlibExt
