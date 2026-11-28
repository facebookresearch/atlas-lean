/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.BraunTree
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Common
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Complete and almost-complete binary trees

The binary-tree size machinery of *Functional Data Structures and
Algorithms*, Chapter 4 (§4.1–§4.3), as formalised in Isabelle's
`HOL-Data_Structures`: `size1` (the number of leaves, `|t|₁`),
`minHeight` (the shortest root-to-leaf path, `mh`), `complete`
(all root-to-leaf paths have equal length), and `acomplete`
(`height t ≤ minHeight t + 1`).

The fundamental bounds (`height t ≤ size t`,
`minHeight t ≤ height t`, `2 ^ minHeight t ≤ size1 t`,
`size1 t ≤ 2 ^ height t`), Lemmas 4.1–4.8 (in particular
`acomplete_optimal` and `height_acomplete`:
`height t = Nat.clog 2 (size1 t)` for `acomplete t`), and the
discrete logarithm `nlog2 n = Nat.clog 2 n` with its identification
with the AFP's `nat (ceiling (log 2 n))` (`nlog2_eq_natCeil_logb`).

`acomplete_if_braun`: every Braun tree is almost complete. It is the
bridge from the Braun invariant to logarithmic height, and the
ingredient of the sorting log bounds in `BraunTree.Sorting`. Its
proof is strong induction on `size (Node l x r)` using the children
and the cross Braun nodes; the `(r₁, l₂)` size pairing is false in
general, so the proof uses the reverse pairing
`(size l₂ = size r₁ ∨ size l₂ = size r₁ + 1)` (`size_pair_disj`),
whose Braun cross node supplies the needed cross inequality.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean.BraunTree.Complete

open BraunTree

variable {α : Type u}





variable {α : Type u}

/-- Book §4.1: `size1`, the number of leaves: `size1 t = size t + 1`. -/
def size1 : BraunTree α → ℕ
  | .Leaf => 1
  | .Node l _ r => size1 l + size1 r

/-- Book §4.1: `size1 t = size t + 1`. -/
theorem size1_size (t : BraunTree α) : size1 t = size t + 1 := by
  induction t with
  | Leaf => rfl
  | Node l _ r ihl ihr => simp only [size1, size, ihl, ihr]; omega

/-- Book §4.1: `minHeight` (`mh`), the shortest root-to-leaf path. -/
def minHeight : BraunTree α → ℕ
  | .Leaf => 0
  | .Node l _ r => min (minHeight l) (minHeight r) + 1

/-- Book §4.2: `complete`: all leaves on the same level. -/
def complete : BraunTree α → Prop
  | .Leaf => True
  | .Node l _ r => height l = height r ∧ complete l ∧ complete r

/-- Book §4.3: `acomplete`: leaves may be on the lowest level or one
    above. -/
def acomplete (t : BraunTree α) : Prop := height t ≤ minHeight t + 1

/-! ### Book §4.1: fundamental properties ("we will simply use these
    fundamental properties without referring to them by a name") -/

/-- `h t ≤ |t|`. -/
theorem height_le_size (t : BraunTree α) : height t ≤ size t := by
  induction t with
  | Leaf => simp [height, size]
  | Node l _ r ihl ihr => simp only [height, size]; omega

/-- `mh t ≤ h t`. -/
theorem minHeight_le_height (t : BraunTree α) : minHeight t ≤ height t := by
  induction t with
  | Leaf => simp [minHeight, height]
  | Node l _ r ihl ihr => simp only [minHeight, height]; omega

/-- `2 ^ (mh t) ≤ |t|₁`. -/
theorem pow_minHeight_le_size1 (t : BraunTree α) : 2 ^ minHeight t ≤ size1 t := by
  induction t with
  | Leaf => simp [minHeight, size1]
  | Node l _ r ihl ihr =>
      simp only [minHeight, size1]
      have hpow : 2 ^ (min (minHeight l) (minHeight r) + 1) =
          2 * 2 ^ min (minHeight l) (minHeight r) := by rw [pow_succ, mul_comm]
      rw [hpow]
      have h1 : 2 ^ min (minHeight l) (minHeight r) ≤ 2 ^ minHeight l :=
        Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)
      have h2 : 2 ^ min (minHeight l) (minHeight r) ≤ 2 ^ minHeight r :=
        Nat.pow_le_pow_right (by norm_num) (min_le_right _ _)
      omega

/-- `|t|₁ ≤ 2 ^ (h t)`. -/
theorem size1_le_pow_height (t : BraunTree α) : size1 t ≤ 2 ^ height t := by
  induction t with
  | Leaf => simp [size1, height]
  | Node l _ r ihl ihr =>
      simp only [size1, height]
      have hpow : 2 ^ (max (height l) (height r) + 1) =
          2 * 2 ^ max (height l) (height r) := by rw [pow_succ, mul_comm]
      rw [hpow]
      have h1 : 2 ^ height l ≤ 2 ^ max (height l) (height r) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
      have h2 : 2 ^ height r ≤ 2 ^ max (height l) (height r) :=
        Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
      omega

/-! ### Book §4.2: complete trees -/

/-- Lemma 4.1: `complete t → mh t = h t`. -/
theorem complete_minHeight_eq_height {t : BraunTree α} (h : complete t) :
    minHeight t = height t := by
  induction t with
  | Leaf => rfl
  | Node l _ r ihl ihr =>
      simp only [complete] at h
      obtain ⟨heq, hcl, hcr⟩ := h
      have h1 := ihl hcl
      have h2 := ihr hcr
      simp only [minHeight, height, h1, h2]
      omega

/-- Lemma 4.2: `complete t → |t|₁ = 2 ^ (h t)`. -/
theorem complete_size1_eq_pow_height {t : BraunTree α} (h : complete t) :
    size1 t = 2 ^ height t := by
  induction t with
  | Leaf => simp [size1, height]
  | Node l _ r ihl ihr =>
      simp only [complete] at h
      obtain ⟨heq, hcl, hcr⟩ := h
      have h1 := ihl hcl
      have h2 := ihr hcr
      simp only [size1, height]
      have hpow : 2 ^ (max (height l) (height r) + 1) = 2 * 2 ^ height l := by
        rw [heq, max_self, pow_succ, mul_comm]
      rw [hpow, h1, h2, heq]
      omega

/-- Lemma 4.3: `¬complete t → |t|₁ < 2 ^ (h t)`. -/
theorem not_complete_size1_lt_pow_height {t : BraunTree α} (h : ¬ complete t) :
    size1 t < 2 ^ height t := by
  induction t with
  | Leaf => simp [complete] at h
  | Node l a r ihl ihr =>
      simp only [complete] at h
      by_cases heq : height l = height r
      · by_cases hcl : complete l
        · have hcr : ¬ complete r := by
            intro hcr; exact h ⟨heq, hcl, hcr⟩
          have ihr' := ihr hcr
          rw [← heq] at ihr'
          have hle : size1 l ≤ 2 ^ height l := size1_le_pow_height l
          have hpow : 2 ^ (max (height l) (height r) + 1) = 2 * 2 ^ height l := by
            rw [heq, max_self, pow_succ, mul_comm]
          simp only [size1, height, hpow]
          omega
        · have ihl' := ihl hcl
          have hle2 : size1 r ≤ 2 ^ height r := size1_le_pow_height r
          rw [← heq] at hle2
          have hpow : 2 ^ (max (height l) (height r) + 1) = 2 * 2 ^ height l := by
            rw [heq, max_self, pow_succ, mul_comm]
          simp only [size1, height, hpow]
          omega
      · rcases lt_or_gt_of_ne heq with hlt | hgt
        · have hle : size1 l ≤ 2 ^ height l := size1_le_pow_height l
          have hle2 : size1 r ≤ 2 ^ height r := size1_le_pow_height r
          have hpow_lt : 2 ^ height l < 2 ^ height r :=
            Nat.pow_lt_pow_right (by norm_num) hlt
          have hmax : max (height l) (height r) = height r :=
            max_eq_right (le_of_lt hlt)
          have hpow : 2 ^ (max (height l) (height r) + 1) = 2 * 2 ^ height r := by
            rw [hmax, pow_succ, mul_comm]
          simp only [size1, height, hpow]
          omega
        · have hle : size1 l ≤ 2 ^ height l := size1_le_pow_height l
          have hle2 : size1 r ≤ 2 ^ height r := size1_le_pow_height r
          have hpow_lt : 2 ^ height r < 2 ^ height l :=
            Nat.pow_lt_pow_right (by norm_num) hgt
          have hmax : max (height l) (height r) = height l :=
            max_eq_left (le_of_lt hgt)
          have hpow : 2 ^ (max (height l) (height r) + 1) = 2 * 2 ^ height l := by
            rw [hmax, pow_succ, mul_comm]
          simp only [size1, height, hpow]
          omega

/-- Corollary 4.5: `complete t ↔ |t|₁ = 2 ^ (h t)`. -/
theorem complete_iff_size1_eq_pow_height {t : BraunTree α} :
    complete t ↔ size1 t = 2 ^ height t := by
  constructor
  · exact complete_size1_eq_pow_height
  · intro h
    by_contra hnc
    have hlt := not_complete_size1_lt_pow_height hnc
    omega

/-- Helper for Lemma 4.4: if one side's `2 ^ minHeight` is strictly
    below its `size1`, the doubled minimum stays below the sum. -/
theorem two_pow_min_minHeight_lt {l r : BraunTree α}
    (h1 : 2 ^ min (minHeight l) (minHeight r) < size1 l)
    (h2 : 2 ^ min (minHeight l) (minHeight r) ≤ size1 r) :
    2 ^ (min (minHeight l) (minHeight r) + 1) < size1 l + size1 r := by
  have hpow : 2 ^ (min (minHeight l) (minHeight r) + 1) =
      2 * 2 ^ min (minHeight l) (minHeight r) := by rw [pow_succ, mul_comm]
  rw [hpow]
  omega

/-- Auxiliary for Lemma 4.4: the case `height l < height r`. The
    symmetric case follows by swapping `l` and `r`. -/
theorem not_complete_pow_minHeight_lt_size1_aux {l r : BraunTree α} (a : α)
    (_h : ¬ complete (BraunTree.Node l a r)) (hlt : height l < height r)
    (_ihl : ¬ complete l → 2 ^ minHeight l < size1 l)
    (ihr : ¬ complete r → 2 ^ minHeight r < size1 r) :
    2 ^ minHeight (BraunTree.Node l a r) < size1 (BraunTree.Node l a r) := by
  by_cases hminle : minHeight l ≤ minHeight r
  · -- `min = minHeight l`; need `2 ^ minHeight l < size1 r`.
    have hstrict : 2 ^ min (minHeight l) (minHeight r) < size1 r := by
      have hmin : min (minHeight l) (minHeight r) = minHeight l := min_eq_left hminle
      rw [hmin]
      by_cases hltmin : minHeight l < minHeight r
      · have hpow : 2 ^ minHeight l < 2 ^ minHeight r :=
          Nat.pow_lt_pow_right (by norm_num) hltmin
        have hfund : 2 ^ minHeight r ≤ size1 r := pow_minHeight_le_size1 r
        omega
      · have heqmin : minHeight l = minHeight r := by omega
        by_cases hcr : complete r
        · have h41 := complete_minHeight_eq_height hcr
          have hle2 : minHeight l ≤ height l := minHeight_le_height l
          omega
        · have ihr' := ihr hcr
          rw [← heqmin] at ihr'
          exact ihr'
    have hle : 2 ^ min (minHeight l) (minHeight r) ≤ size1 l := by
      have hmin : min (minHeight l) (minHeight r) ≤ minHeight l := min_le_left _ _
      have hpow : 2 ^ min (minHeight l) (minHeight r) ≤ 2 ^ minHeight l :=
        Nat.pow_le_pow_right (by norm_num) hmin
      have hfund : 2 ^ minHeight l ≤ size1 l := pow_minHeight_le_size1 l
      omega
    -- Apply the helper to `(r, l)` (strict on the right) and commute.
    have hres := two_pow_min_minHeight_lt (l := r) (r := l)
      (by rw [min_comm]; exact hstrict) (by rw [min_comm]; exact hle)
    rw [min_comm (minHeight r) (minHeight l), add_comm (size1 r) (size1 l)] at hres
    simp only [minHeight, size1]
    exact hres
  · -- `minHeight l > minHeight r`, so `min = minHeight r`.
    have hstrict : 2 ^ min (minHeight l) (minHeight r) < size1 l := by
      have hmin : min (minHeight l) (minHeight r) = minHeight r :=
        min_eq_right (le_of_lt (by omega : minHeight r < minHeight l))
      rw [hmin]
      have hpow : 2 ^ minHeight r < 2 ^ minHeight l :=
        Nat.pow_lt_pow_right (by norm_num) (by omega)
      have hfund : 2 ^ minHeight l ≤ size1 l := pow_minHeight_le_size1 l
      omega
    have hle : 2 ^ min (minHeight l) (minHeight r) ≤ size1 r := by
      have hmin : min (minHeight l) (minHeight r) ≤ minHeight r := min_le_right _ _
      have hpow : 2 ^ min (minHeight l) (minHeight r) ≤ 2 ^ minHeight r :=
        Nat.pow_le_pow_right (by norm_num) hmin
      have hfund : 2 ^ minHeight r ≤ size1 r := pow_minHeight_le_size1 r
      omega
    have hres := two_pow_min_minHeight_lt hstrict hle
    simp only [minHeight, size1]
    exact hres

/-- Lemma 4.4: `¬complete t → 2 ^ (mh t) < |t|₁`. -/
theorem not_complete_pow_minHeight_lt_size1 {t : BraunTree α} (h : ¬ complete t) :
    2 ^ minHeight t < size1 t := by
  induction t with
  | Leaf => simp [complete] at h
  | Node l a r ihl ihr =>
      simp only [complete] at h
      rcases lt_trichotomy (height l) (height r) with hlt | heq | hgt
      · exact not_complete_pow_minHeight_lt_size1_aux a h hlt ihl ihr
      · -- `height l = height r`, so `¬complete l ∨ ¬complete r`.
        by_cases hcl : complete l
        · have hcr : ¬ complete r := by
            intro hcr; exact h ⟨heq, hcl, hcr⟩
          have ihr' := ihr hcr
          have hstrict : 2 ^ min (minHeight l) (minHeight r) < size1 r := by
            have hmin : min (minHeight l) (minHeight r) ≤ minHeight r := min_le_right _ _
            have hpow : 2 ^ min (minHeight l) (minHeight r) ≤ 2 ^ minHeight r :=
              Nat.pow_le_pow_right (by norm_num) hmin
            omega
          have hle : 2 ^ min (minHeight l) (minHeight r) ≤ size1 l := by
            have hmin : min (minHeight l) (minHeight r) ≤ minHeight l := min_le_left _ _
            have hpow : 2 ^ min (minHeight l) (minHeight r) ≤ 2 ^ minHeight l :=
              Nat.pow_le_pow_right (by norm_num) hmin
            have hfund : 2 ^ minHeight l ≤ size1 l := pow_minHeight_le_size1 l
            omega
          have hres := two_pow_min_minHeight_lt (l := r) (r := l)
            (by rw [min_comm]; exact hstrict) (by rw [min_comm]; exact hle)
          rw [min_comm (minHeight r) (minHeight l), add_comm (size1 r) (size1 l)] at hres
          simp only [minHeight, size1]
          exact hres
        · have ihl' := ihl hcl
          have hstrict : 2 ^ min (minHeight l) (minHeight r) < size1 l := by
            have hmin : min (minHeight l) (minHeight r) ≤ minHeight l := min_le_left _ _
            have hpow : 2 ^ min (minHeight l) (minHeight r) ≤ 2 ^ minHeight l :=
              Nat.pow_le_pow_right (by norm_num) hmin
            omega
          have hle : 2 ^ min (minHeight l) (minHeight r) ≤ size1 r := by
            have hmin : min (minHeight l) (minHeight r) ≤ minHeight r := min_le_right _ _
            have hpow : 2 ^ min (minHeight l) (minHeight r) ≤ 2 ^ minHeight r :=
              Nat.pow_le_pow_right (by norm_num) hmin
            have hfund : 2 ^ minHeight r ≤ size1 r := pow_minHeight_le_size1 r
            omega
          have hres := two_pow_min_minHeight_lt hstrict hle
          simp only [minHeight, size1]
          exact hres
      · -- `height r < height l`: symmetric, via the auxiliary lemma
        -- with `l` and `r` swapped.
        have h' : ¬ complete (BraunTree.Node r a l) := by
          intro hc
          apply h
          simp only [complete] at hc ⊢
          obtain ⟨h1, h2, h3⟩ := hc
          exact ⟨h1.symm, h3, h2⟩
        have haux := not_complete_pow_minHeight_lt_size1_aux (l := r) (r := l) (a := a)
          h' hgt ihr ihl
        simp only [minHeight, size1,
          min_comm (minHeight r) (minHeight l), add_comm (size1 r) (size1 l)] at haux
        simp only [minHeight, size1]
        exact haux

/-! ### Book §4.3: almost complete trees -/

/-- Lemma 4.6 (`acomplete_optimal`): almost complete trees have
    minimal height among trees with at least as many nodes. -/
theorem acomplete_optimal {s t : BraunTree α} (hs : acomplete s)
    (hsize : size s ≤ size t) : height s ≤ height t := by
  by_cases hc : complete s
  · have h2 := complete_size1_eq_pow_height hc
    have h1 : size1 s ≤ size1 t := by
      rw [size1_size, size1_size]; omega
    have h3 : size1 t ≤ 2 ^ height t := size1_le_pow_height t
    rw [h2] at h1
    -- `2 ^ height s ≤ 2 ^ height t` implies `height s ≤ height t`.
    by_contra hgt
    push Not at hgt
    have hpow : 2 ^ height t < 2 ^ height s := Nat.pow_lt_pow_right (by norm_num) hgt
    omega
  · have h4 := not_complete_pow_minHeight_lt_size1 hc
    have h1 : size1 s ≤ size1 t := by
      rw [size1_size, size1_size]; omega
    have h3 : size1 t ≤ 2 ^ height t := size1_le_pow_height t
    -- `height s = minHeight s + 1`: from `acomplete s`, `minHeight s ≤
    -- height s`, and `minHeight s ≠ height s` (else `s` would be
    -- complete, by Corollary 4.5).
    have hne : minHeight s ≠ height s := by
      intro heq
      apply hc
      apply (complete_iff_size1_eq_pow_height).mpr
      have hle1 : 2 ^ height s ≤ size1 s := by
        rw [← heq]; exact pow_minHeight_le_size1 s
      have hle2 : size1 s ≤ 2 ^ height s := size1_le_pow_height s
      omega
    have hmh : minHeight s ≤ height s := minHeight_le_height s
    have hheight : height s = minHeight s + 1 := by
      have hac : height s ≤ minHeight s + 1 := hs
      omega
    -- `minHeight s < height t` from `2 ^ minHeight s < size1 s ≤
    -- size1 t ≤ 2 ^ height t`.
    have hlt : minHeight s < height t := by
      by_contra hge
      push Not at hge
      have hpow : 2 ^ height t ≤ 2 ^ minHeight s :=
        Nat.pow_le_pow_right (by norm_num) hge
      omega
    omega

/-- Lemma 4.7 (`height_acomplete`): the closed form for the height
    of an almost complete tree. -/
theorem height_acomplete {t : BraunTree α} (h : acomplete t) :
    height t = Nat.clog 2 (size1 t) := by
  by_cases hc : complete t
  · rw [complete_size1_eq_pow_height hc]
    exact (Nat.clog_pow 2 (height t) (by norm_num)).symm
  · have h4 := not_complete_pow_minHeight_lt_size1 hc
    have hne : minHeight t ≠ height t := by
      intro heq
      apply hc
      apply (complete_iff_size1_eq_pow_height).mpr
      have hle1 : 2 ^ height t ≤ size1 t := by
        rw [← heq]; exact pow_minHeight_le_size1 t
      have hle2 : size1 t ≤ 2 ^ height t := size1_le_pow_height t
      omega
    have hmh : minHeight t ≤ height t := minHeight_le_height t
    have hheight : height t = minHeight t + 1 := by
      have hac : height t ≤ minHeight t + 1 := h
      omega
    have hle : size1 t ≤ 2 ^ (minHeight t + 1) := by
      have h1 : size1 t ≤ 2 ^ height t := size1_le_pow_height t
      rw [hheight] at h1
      exact h1
    -- `minHeight t < Nat.clog 2 (size1 t) ≤ minHeight t + 1`.
    have hlt : minHeight t < Nat.clog 2 (size1 t) := by
      rw [Nat.lt_clog_iff_pow_lt (by norm_num)]
      exact h4
    have hle2 : Nat.clog 2 (size1 t) ≤ minHeight t + 1 := by
      rw [Nat.clog_le_iff_le_pow (by norm_num)]
      exact hle
    omega

/-- Lemma 4.8: the closed form for the minimal height of an almost
    complete tree. -/
theorem minHeight_eq_log_of_acomplete {t : BraunTree α} (h : acomplete t) :
    minHeight t = Nat.log 2 (size1 t) := by
  by_cases hc : complete t
  · rw [complete_minHeight_eq_height hc, complete_size1_eq_pow_height hc]
    exact (Nat.log_pow (by norm_num : (1:ℕ) < 2) (height t)).symm
  · have hne : minHeight t ≠ height t := by
      intro heq
      apply hc
      apply (complete_iff_size1_eq_pow_height).mpr
      have hle1 : 2 ^ height t ≤ size1 t := by
        rw [← heq]; exact pow_minHeight_le_size1 t
      have hle2 : size1 t ≤ 2 ^ height t := size1_le_pow_height t
      omega
    have hmh : minHeight t ≤ height t := minHeight_le_height t
    have hheight : height t = minHeight t + 1 := by
      have hac : height t ≤ minHeight t + 1 := h
      omega
    have h4 := not_complete_pow_minHeight_lt_size1 hc
    -- `size1 t < 2 ^ (minHeight t + 1)`: else `size1 t = 2 ^ (height t)`
    -- and `t` would be complete, by Corollary 4.5.
    have hlt2 : size1 t < 2 ^ (minHeight t + 1) := by
      have hle : size1 t ≤ 2 ^ (minHeight t + 1) := by
        have h1 : size1 t ≤ 2 ^ height t := size1_le_pow_height t
        rw [hheight] at h1
        exact h1
      by_contra hge
      push Not at hge
      have heq : size1 t = 2 ^ (minHeight t + 1) := by omega
      apply hc
      apply (complete_iff_size1_eq_pow_height).mpr
      rw [hheight]
      exact heq
    exact (Nat.log_eq_of_pow_le_of_lt_pow
      (by exact le_of_lt h4) hlt2).symm

/-! ### Chapter 2: the ceiling discrete log `dlg` = the AFP's `nlog2` -/

/-- AFP `nlog2`: `nlog2 n = nat (ceiling (log 2 n))`, i.e. Chapter 2's
    ceiling discrete log `dlg`. -/
def nlog2 (n : ℕ) : ℕ := Nat.clog 2 n

/-- The bridge to Isabelle's definition: `nlog2 n` is the natural
    ceiling of the real base-2 logarithm. -/
theorem nlog2_eq_natCeil_logb (n : ℕ) :
    nlog2 n = ⌈Real.logb 2 (n : ℝ)⌉₊ := by
  change Nat.clog 2 n = ⌈Real.logb ((2 : ℕ) : ℝ) (n : ℝ)⌉₊
  rw [Real.natCeil_logb_natCast]

/-- Size comparison for the components of two Braun nodes: from the
    three size disjunctions (`a` vs `b`, `c` vs `d`, `a+b` vs `c+d`),
    the pairings `(a,c)`, `(a,d)` and `(b,d)` satisfy the same disjunction pattern.
    This is pure linear arithmetic (`omega` over the eight cases). -/
theorem size_pair_disj {a b c d : ℕ}
    (h1 : a = b ∨ a = b + 1) (h2 : c = d ∨ c = d + 1)
    (h3 : a + b = c + d ∨ a + b = c + d + 1) :
    (a = c ∨ a = c + 1) ∧ (a = d ∨ a = d + 1) ∧
    (b = d ∨ b = d + 1) ∧ (c = b ∨ c = b + 1) := by
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> omega

/-- Joint proof of `braun_height_r_le` and `braun_height_l_le`, by
    strong induction on `size (Node l x r)`. The four cross Braun
    nodes `(Node l₁ ? l₂)`, `(Node l₁ ? r₂)`, `(Node r₁ ? l₂)`,
    `(Node r₁ ? r₂)` are all Braun (by `size_pair_disj`) and
    strictly smaller, so the induction hypotheses give both height
    inequalities for every pair of children. -/
theorem braun_height_both_aux : ∀ (m : ℕ) (l : BraunTree α) (x : α) (r : BraunTree α),
    size (BraunTree.Node l x r) = m → Braun (BraunTree.Node l x r) →
    height r ≤ height l ∧ height l ≤ height r + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro l x r hsize hb
      cases l with
      | Leaf =>
          cases r with
          | Leaf => simp [height]
          | Node l₂ x₂ r₂ =>
              exfalso
              rw [braun_node] at hb
              simp only [size] at hb
              omega
      | Node l₁ x₁ r₁ =>
          cases r with
          | Leaf =>
              rw [braun_node] at hb
              obtain ⟨hsz, _ , _⟩ := hb
              have h0 : size l₁ + size r₁ = 0 := by
                simp only [size] at hsz ⊢
                omega
              have hl1 : l₁ = BraunTree.Leaf := by
                have : size l₁ = 0 := by omega
                exact (size_eq_zero).mp this
              have hr1 : r₁ = BraunTree.Leaf := by
                have : size r₁ = 0 := by omega
                exact (size_eq_zero).mp this
              subst hl1
              subst hr1
              simp [height]
          | Node l₂ x₂ r₂ =>
              rw [braun_node] at hb
              obtain ⟨hsz_outer, hbl, hbr⟩ := hb
              rw [braun_node] at hbl hbr
              obtain ⟨hs1, hbl1, hbr1⟩ := hbl
              obtain ⟨hs2, hbl2, hbr2⟩ := hbr
              have hsL : size (BraunTree.Node l₁ x₁ r₁) = size l₁ + size r₁ + 1 := rfl
              have hsR : size (BraunTree.Node l₂ x₂ r₂) = size l₂ + size r₂ + 1 := rfl
              obtain ⟨hp1, hp2, hp3, -⟩ := size_pair_disj hs1 hs2 (by omega)
              have hb_ll : Braun (BraunTree.Node l₁ x₁ l₂) :=
                braun_node.mpr ⟨hp1, hbl1, hbl2⟩
              have hb_lr : Braun (BraunTree.Node l₁ x₁ r₂) :=
                braun_node.mpr ⟨hp2, hbl1, hbr2⟩
              have hb_rr : Braun (BraunTree.Node r₁ x₁ r₂) :=
                braun_node.mpr ⟨hp3, hbr1, hbr2⟩
              have hlt_ll : size (BraunTree.Node l₁ x₁ l₂) < m := by
                simp only [size] at hsize ⊢
                omega
              have hlt_lr : size (BraunTree.Node l₁ x₁ r₂) < m := by
                simp only [size] at hsize ⊢
                omega
              have hlt_rr : size (BraunTree.Node r₁ x₁ r₂) < m := by
                simp only [size] at hsize ⊢
                omega
              have ih_ll := ih _ hlt_ll l₁ x₁ l₂ rfl hb_ll
              have ih_lr := ih _ hlt_lr l₁ x₁ r₂ rfl hb_lr
              have ih_rr := ih _ hlt_rr r₁ x₁ r₂ rfl hb_rr
              constructor <;> simp only [height] at * <;> omega

/-- AFP lemma `braun_height_r_le`. -/
theorem braun_height_r_le {l : BraunTree α} {x : α} {r : BraunTree α}
    (hb : Braun (BraunTree.Node l x r)) : height r ≤ height l :=
  (braun_height_both_aux _ l x r rfl hb).1

/-- AFP lemma `braun_height_l_le`. -/
theorem braun_height_l_le {l : BraunTree α} {x : α} {r : BraunTree α}
    (hb : Braun (BraunTree.Node l x r)) : height l ≤ height r + 1 :=
  (braun_height_both_aux _ l x r rfl hb).2

/-- AFP lemma `braun_height_node_eq`. -/
theorem braun_height_node_eq {l : BraunTree α} {x : α} {r : BraunTree α}
    (hb : Braun (BraunTree.Node l x r)) :
    height (BraunTree.Node l x r) = height l + 1 := by
  have hle := braun_height_r_le hb
  simp only [height]
  omega

/-- AFP lemma `acomplete_if_braun`: every Braun tree is almost
    complete. Proved by strong induction on `size (Node l x r)`, using
    the two children and the four cross Braun nodes (as in
    `braun_height_both_aux`): the induction hypotheses give every
    cross inequality between the children's heights and min-heights. -/
theorem acomplete_if_braun_aux : ∀ (m : ℕ) (l : BraunTree α) (x : α) (r : BraunTree α),
    size (BraunTree.Node l x r) = m → Braun (BraunTree.Node l x r) →
    height (BraunTree.Node l x r) ≤ minHeight (BraunTree.Node l x r) + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
      intro l x r hsize hb
      cases l with
      | Leaf =>
          cases r with
          | Leaf => simp [height, minHeight]
          | Node l₂ x₂ r₂ =>
              exfalso
              rw [braun_node] at hb
              simp only [size] at hb
              omega
      | Node l₁ x₁ r₁ =>
          cases r with
          | Leaf =>
              rw [braun_node] at hb
              obtain ⟨hsz, _, _⟩ := hb
              have h0 : size l₁ + size r₁ = 0 := by
                simp only [size] at hsz ⊢
                omega
              have hl1 : l₁ = BraunTree.Leaf := (size_eq_zero).mp (by omega)
              have hr1 : r₁ = BraunTree.Leaf := (size_eq_zero).mp (by omega)
              subst hl1
              subst hr1
              simp [height, minHeight]
          | Node l₂ x₂ r₂ =>
              rw [braun_node] at hb
              obtain ⟨hsz_outer, hbl, hbr⟩ := hb
              rw [braun_node] at hbl hbr
              obtain ⟨hs1, hbl1, hbr1⟩ := hbl
              obtain ⟨hs2, hbl2, hbr2⟩ := hbr
              have hsL : size (BraunTree.Node l₁ x₁ r₁) = size l₁ + size r₁ + 1 := rfl
              have hsR : size (BraunTree.Node l₂ x₂ r₂) = size l₂ + size r₂ + 1 := rfl
              obtain ⟨hp1, hp2, hp3, hp4⟩ := size_pair_disj hs1 hs2 (by omega)
              have hb_ll : Braun (BraunTree.Node l₁ x₁ l₂) :=
                braun_node.mpr ⟨hp1, hbl1, hbl2⟩
              have hb_lr : Braun (BraunTree.Node l₁ x₁ r₂) :=
                braun_node.mpr ⟨hp2, hbl1, hbr2⟩
              -- The (r₁,l₂) pairing is false in general; the reverse
              -- pairing (l₂,r₁) is the one that holds, and its IH gives
              -- `height l₂ ≤ minHeight r₁ + 1`.
              have hb_l2r1 : Braun (BraunTree.Node l₂ x₁ r₁) :=
                braun_node.mpr ⟨hp4, hbl2, hbr1⟩
              have hb_rr : Braun (BraunTree.Node r₁ x₁ r₂) :=
                braun_node.mpr ⟨hp3, hbr1, hbr2⟩
              have hlt_ll : size (BraunTree.Node l₁ x₁ l₂) < m := by
                simp only [size] at hsize ⊢
                omega
              have hlt_lr : size (BraunTree.Node l₁ x₁ r₂) < m := by
                simp only [size] at hsize ⊢
                omega
              have hlt_l2r1 : size (BraunTree.Node l₂ x₁ r₁) < m := by
                simp only [size] at hsize ⊢
                omega
              have hlt_rr : size (BraunTree.Node r₁ x₁ r₂) < m := by
                simp only [size] at hsize ⊢
                omega
              have hlt_L : size (BraunTree.Node l₁ x₁ r₁) < m := by
                simp only [size] at hsize ⊢
                omega
              have hlt_R : size (BraunTree.Node l₂ x₂ r₂) < m := by
                simp only [size] at hsize ⊢
                omega
              have ih_ll := ih _ hlt_ll l₁ x₁ l₂ rfl hb_ll
              have ih_lr := ih _ hlt_lr l₁ x₁ r₂ rfl hb_lr
              have ih_l2r1 := ih _ hlt_l2r1 l₂ x₁ r₁ rfl hb_l2r1
              have ih_rr := ih _ hlt_rr r₁ x₁ r₂ rfl hb_rr
              have ih_L := ih _ hlt_L l₁ x₁ r₁ rfl (braun_node.mpr ⟨hs1, hbl1, hbr1⟩)
              have ih_R := ih _ hlt_R l₂ x₂ r₂ rfl (braun_node.mpr ⟨hs2, hbl2, hbr2⟩)
              simp only [height, minHeight] at ih_ll ih_lr ih_l2r1 ih_rr ih_L ih_R
              have h_a : height l₁ ≤ minHeight l₂ + 1 := by omega
              have h_b : height l₁ ≤ minHeight r₂ + 1 := by omega
              have h_c : height l₁ ≤ minHeight l₁ + 1 := by omega
              have h_d : height l₁ ≤ minHeight r₁ + 1 := by omega
              have h_e : height l₂ ≤ minHeight l₁ + 1 := by omega
              have h_f : height l₂ ≤ minHeight r₁ + 1 := by omega
              have h_g : height l₂ ≤ minHeight l₂ + 1 := by omega
              have h_h : height l₂ ≤ minHeight r₂ + 1 := by omega
              have hL : height (BraunTree.Node l₁ x₁ r₁) = height l₁ + 1 :=
                braun_height_node_eq (braun_node.mpr ⟨hs1, hbl1, hbr1⟩)
              have hR : height (BraunTree.Node l₂ x₂ r₂) = height l₂ + 1 :=
                braun_height_node_eq (braun_node.mpr ⟨hs2, hbl2, hbr2⟩)
              have hgoal1 : height (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) x
                  (BraunTree.Node l₂ x₂ r₂)) =
                  max (height l₁) (height l₂) + 2 := by
                have h1 : height (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) x
                    (BraunTree.Node l₂ x₂ r₂)) =
                    max (height (BraunTree.Node l₁ x₁ r₁))
                      (height (BraunTree.Node l₂ x₂ r₂)) + 1 := rfl
                rw [h1, hL, hR, max_add_add_right]
              have hgoal2 : minHeight (BraunTree.Node (BraunTree.Node l₁ x₁ r₁) x
                  (BraunTree.Node l₂ x₂ r₂)) =
                  min (min (minHeight l₁) (minHeight r₁))
                    (min (minHeight l₂) (minHeight r₂)) + 2 := by
                simp only [minHeight]
                omega
              -- Combine the eight linear inequalities with `max_le` /
              -- `le_min` instead of `omega`, which splits every nested
              -- `max` / `min` and times out here.
              have hk1 : height l₁ ≤
                  min (min (minHeight l₁) (minHeight r₁))
                    (min (minHeight l₂) (minHeight r₂)) + 1 := by
                rw [← min_add_add_right]
                apply le_min
                · rw [← min_add_add_right]
                  exact le_min h_c h_d
                · rw [← min_add_add_right]
                  exact le_min h_a h_b
              have hk2 : height l₂ ≤
                  min (min (minHeight l₁) (minHeight r₁))
                    (min (minHeight l₂) (minHeight r₂)) + 1 := by
                rw [← min_add_add_right]
                apply le_min
                · rw [← min_add_add_right]
                  exact le_min h_e h_f
                · rw [← min_add_add_right]
                  exact le_min h_g h_h
              have hmax : max (height l₁) (height l₂) ≤
                  min (min (minHeight l₁) (minHeight r₁)) (min (minHeight l₂) (minHeight r₂)) + 1 :=
                max_le hk1 hk2
              rw [hgoal1, hgoal2]
              exact Nat.add_le_add_right hmax 2

/-- AFP lemma `acomplete_if_braun`: Braun trees are almost complete. -/
theorem acomplete_if_braun {t : BraunTree α} (ht : Braun t) : acomplete t := by
  cases t with
  | Leaf => simp [acomplete, height, minHeight]
  | Node l a r => exact acomplete_if_braun_aux _ l a r rfl ht

end Cslib.Algorithms.Lean.BraunTree.Complete
