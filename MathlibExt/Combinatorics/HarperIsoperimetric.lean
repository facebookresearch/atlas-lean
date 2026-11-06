/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.HammingExpansion
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Find
import Mathlib.InformationTheory.Hamming
import Mathlib.Tactic.LinearCombination

@[expose] public section

section
namespace MathlibExt.Combinatorics.HarperIsoperimetricWanted

/-!
# Harper isoperimetric inequality, ball-comparison form
Scope: the ball-comparison specialization only, over `{0, 1}^n` with closed
expansions at positive natural radii.

ATLAS item N134 (ProbabilisticMethodsInCombinatorics:134). Source:
`Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/HarperIsoperimetric.lean`.

Source-to-API map: source lines 42--51 correspond to
`harper_isoperimetric_inequality`, using `Hamming.expansion` and
`Hamming.IsBall` for the definitions at lines 17--39.

This is the full ATLAS N134 ball-comparison target, but not the stronger
simplicial-order or equality-case characterization.
-/

private theorem hammingDist_eq_filter_card {ι F : Type*} [Fintype ι] [DecidableEq F]
    (x y : ι → F) :
    hammingDist x y = (Finset.univ.filter fun i => x i ≠ y i).card := by
  rw [hammingDist]

private theorem expansion_ball_subset {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype F] [DecidableEq F] (c : ι → F) (e t : ℕ) :
    Hamming.expansion (Hamming.ball c e) t ⊆ Hamming.ball c (e + t) := by
  intro x hx
  rw [Hamming.mem_expansion] at hx
  rw [Hamming.mem_ball]
  obtain ⟨a, ha, hxa⟩ := hx
  rw [Hamming.mem_ball] at ha
  calc hammingDist c x ≤ hammingDist c a + hammingDist a x :=
        hammingDist_triangle _ _ _
    _ = hammingDist c a + hammingDist x a := by rw [hammingDist_comm a x]
    _ ≤ e + t := Nat.add_le_add ha hxa

private theorem ball_subset_expansion_ball {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype F] [DecidableEq F] (c : ι → F) (e t : ℕ) :
    Hamming.ball c (e + t) ⊆ Hamming.expansion (Hamming.ball c e) t := by
  intro x hx
  rw [Hamming.mem_ball] at hx
  have hle : (Finset.univ.filter (fun i => x i ≠ c i)).card ≤ e + t := by
    have h := hammingDist_eq_filter_card x c
    rw [hammingDist_comm] at h
    omega
  by_cases hcase : (Finset.univ.filter (fun i => x i ≠ c i)).card ≤ e
  · refine Hamming.mem_expansion.mpr ⟨x, ?_, by simp [hammingDist_self]⟩
    rw [Hamming.mem_ball]
    have h2 : hammingDist c x = (Finset.univ.filter (fun i => x i ≠ c i)).card := by
      rw [hammingDist_comm]; exact hammingDist_eq_filter_card x c
    omega
  · have hlt : e < (Finset.univ.filter (fun i => x i ≠ c i)).card :=
      Nat.lt_of_not_ge hcase
    obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq (le_of_lt hlt)
    set a : ι → F := (fun i => if i ∈ S then x i else c i) with ha
    refine Hamming.mem_expansion.mpr ⟨a, ?_, ?_⟩
    · rw [Hamming.mem_ball]
      have hfilter : (Finset.univ.filter fun i => a i ≠ c i) = S := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, ha]
        by_cases hi : i ∈ S
        · rw [ite_eq_left hi]
          constructor
          · intro _
            exact hi
          · intro _
            have hmem := hSsub hi
            simpa using hmem
        · rw [ite_eq_right hi]
          simp [hi]
      have hdist : hammingDist c a = S.card := by
        rw [hammingDist_comm, hammingDist_eq_filter_card, hfilter]
      omega
    · have hfilter : (Finset.univ.filter fun i => x i ≠ a i) =
        (Finset.univ.filter (fun j => x j ≠ c j)) \ S := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, ha]
        by_cases hi : i ∈ S
        · rw [ite_eq_left hi]
          simp [hi]
        · rw [ite_eq_right hi]
          constructor
          · intro h
            exact ⟨h, hi⟩
          · rintro ⟨h, -⟩
            exact h
      have hdist : hammingDist x a =
          ((Finset.univ.filter (fun j => x j ≠ c j)) \ S).card := by
        rw [hammingDist_eq_filter_card, hfilter]
      rw [hdist, Finset.card_sdiff_of_subset hSsub, hScard]
      omega

private theorem expansion_ball_eq {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype F] [DecidableEq F] (c : ι → F) (e t : ℕ) :
    Hamming.expansion (Hamming.ball c e) t = Hamming.ball c (e + t) :=
  Finset.Subset.antisymm (expansion_ball_subset c e t) (ball_subset_expansion_ball c e t)

/-- Ball volume: partial binomial sum `∑_{i ≤ k} C(n,i)`. -/
private def ballVol (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), n.choose i

private theorem ballVol_zero (n : ℕ) : ballVol n 0 = 1 := by
  simp [ballVol]

private theorem ballVol_succ (n k : ℕ) :
    ballVol n (k + 1) = ballVol n k + n.choose (k + 1) := by
  rw [ballVol, ballVol, Finset.sum_range_succ]

private theorem ballVol_mono {n a b : ℕ} (h : a ≤ b) : ballVol n a ≤ ballVol n b := by
  unfold ballVol
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_subset_range.mpr (by omega)
  · intro i _ _
    exact Nat.zero_le _

private theorem ballVol_pos (n k : ℕ) : 0 < ballVol n k := by
  unfold ballVol
  have h0 : n.choose 0 ≤ ∑ i ∈ Finset.range (k + 1), n.choose i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.zero_lt_succ _))
  simp only [Nat.choose_zero_right] at h0
  omega

private theorem ballVol_strict_succ {n k : ℕ} (h : k + 1 ≤ n) :
    ballVol n k < ballVol n (k + 1) := by
  rw [ballVol_succ]
  have hc : 0 < n.choose (k + 1) := Nat.choose_pos h
  omega

private theorem ballVol_pascal (n k : ℕ) :
    ballVol (n + 1) (k + 1) = ballVol n (k + 1) + ballVol n k := by
  have h1 : ballVol (n + 1) (k + 1)
      = (∑ i ∈ Finset.range (k + 1), n.choose i)
        + (∑ i ∈ Finset.range (k + 1), n.choose (i + 1)) + 1 := by
    unfold ballVol
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_succ_succ', Finset.sum_add_distrib, Nat.choose_zero_right]
  have h2 : ballVol n (k + 1)
      = (∑ i ∈ Finset.range (k + 1), n.choose (i + 1)) + 1 := by
    unfold ballVol
    rw [Finset.sum_range_succ', Nat.choose_zero_right]
  rw [h1, h2]
  unfold ballVol
  ring

private theorem ballVol_eq_pow {n k : ℕ} (h : n ≤ k) : ballVol n k = 2 ^ n := by
  have hsub : Finset.range (n + 1) ⊆ Finset.range (k + 1) :=
    Finset.range_subset_range.mpr (by omega)
  have hsum : (∑ i ∈ Finset.range (n + 1), n.choose i)
      = ∑ i ∈ Finset.range (k + 1), n.choose i := by
    apply Finset.sum_subset hsub
    intro i _ hi
    simp only [Finset.mem_range, not_lt] at hi
    exact Nat.choose_eq_zero_of_lt (by omega)
  rw [ballVol, ← hsum, Nat.sum_range_choose]

private theorem ballVol_le_pow (n k : ℕ) : ballVol n k ≤ 2 ^ n := by
  by_cases h : k ≤ n
  · calc ballVol n k ≤ ballVol n n := ballVol_mono h
      _ = 2 ^ n := ballVol_eq_pow le_rfl
  · have h' : n ≤ k := by omega
    rw [ballVol_eq_pow h']

private theorem ballVol_card_ball {n : ℕ} (c : Fin n → Bool) (e : ℕ) :
    (Hamming.ball c e).card = ballVol n e := by
  rw [Hamming.card_ball, ballVol]
  apply Finset.sum_congr rfl
  intro k _
  simp [Fintype.card_fin, Fintype.card_bool]

private theorem ballVol_strictMono {n a b : ℕ} (hab : a < b) (hb : b ≤ n) :
    ballVol n a < ballVol n b := by
  calc ballVol n a < ballVol n (a + 1) := ballVol_strict_succ (by omega)
    _ ≤ ballVol n b := ballVol_mono (by omega)

/-- Chord index: largest `j ≤ n` with `ballVol n j ≤ m`. -/
private def chordIdx (n m : ℕ) : ℕ :=
  Nat.findGreatest (fun j => ballVol n j ≤ m) n

/-- Chord slope on interval `j`: `C(n,j+2)/C(n,j+1)`. -/
private def chordSlope (n j : ℕ) : ℚ :=
  (n.choose (j + 2) : ℚ) / (n.choose (j + 1) : ℚ)

/-- Chord lower bound on `t = 1` expansion size, as a rational. -/
private def chord (n m : ℕ) : ℚ :=
  if m = 0 then 0
  else (ballVol n (chordIdx n m + 1) : ℚ)
    + chordSlope n (chordIdx n m) * ((m : ℚ) - (ballVol n (chordIdx n m) : ℚ))

private theorem chordIdx_le (n m : ℕ) : chordIdx n m ≤ n :=
  Nat.findGreatest_le n

private theorem chordIdx_mem_lower {n m : ℕ} (hm : 0 < m) :
    ballVol n (chordIdx n m) ≤ m := by
  have h := Nat.findGreatest_spec (P := fun j => ballVol n j ≤ m) (m := 0) (n := n)
    (Nat.zero_le n) (by rw [ballVol_zero]; omega)
  exact h

private theorem chordIdx_mem_upper {n m : ℕ} :
    m < ballVol n (chordIdx n m + 1) ∨ chordIdx n m = n := by
  by_cases h : chordIdx n m < n
  · left
    by_contra hc
    have hle : ballVol n (chordIdx n m + 1) ≤ m := Nat.le_of_not_gt hc
    have hlt : chordIdx n m + 1 ≤ chordIdx n m :=
      Nat.le_findGreatest (by omega) hle
    omega
  · right
    have hle := chordIdx_le n m
    omega

private theorem chordSlope_mul (n j : ℕ) (h : j + 1 ≤ n) :
    chordSlope n j * (n.choose (j + 1) : ℚ) = (n.choose (j + 2) : ℚ) := by
  unfold chordSlope
  have hC : (n.choose (j + 1) : ℚ) ≠ 0 := by
    have hpos : 0 < n.choose (j + 1) := Nat.choose_pos h
    exact_mod_cast ne_of_gt hpos
  field_simp

private theorem chordSlope_cont {n j : ℕ} (hj : j + 1 ≤ n) :
    (ballVol n (j + 1) : ℚ) + chordSlope n j * ((ballVol n (j + 1) : ℚ) - ballVol n j)
      = (ballVol n (j + 2) : ℚ) := by
  have hmul := chordSlope_mul n j hj
  have hV : ballVol n (j + 2) = ballVol n (j + 1) + n.choose (j + 2) := by
    have h := ballVol_succ n (j + 1)
    rwa [show j + 1 + 1 = j + 2 from rfl] at h
  have hV' : ballVol n (j + 1) = ballVol n j + n.choose (j + 1) :=
    ballVol_succ n j
  have hcast : ((ballVol n (j + 1) : ℕ) : ℚ) - (ballVol n j : ℕ)
      = (n.choose (j + 1) : ℚ) := by
    have hq : ((ballVol n (j + 1) : ℕ) : ℚ)
        = ((ballVol n j : ℕ) : ℚ) + (n.choose (j + 1) : ℚ) := by
      exact_mod_cast hV'
    linarith
  rw [hcast]
  have hq2 : ((ballVol n (j + 2) : ℕ) : ℚ)
      = ((ballVol n (j + 1) : ℕ) : ℚ) + (n.choose (j + 2) : ℚ) := by
    exact_mod_cast hV
  rw [hq2]
  linarith [hmul]

private theorem chord_eq_of_mem {n m j : ℕ} (hm0 : m ≠ 0) (hlt : m < 2 ^ n)
    (hj : j < n) (hlo : ballVol n j ≤ m) (hhi : m ≤ ballVol n (j + 1)) :
    chord n m = (ballVol n (j + 1) : ℚ)
      + chordSlope n j * ((m : ℚ) - (ballVol n j : ℚ)) := by
  have hidx : chordIdx n m < n := by
    by_contra hc
    have hle := chordIdx_le n m
    have heq : chordIdx n m = n := by omega
    have hlo' := chordIdx_mem_lower (n := n) (m := m) (by omega)
    rw [heq, ballVol_eq_pow le_rfl] at hlo'
    omega
  have hup : m < ballVol n (chordIdx n m + 1) := by
    rcases chordIdx_mem_upper (n := n) (m := m) with h | h
    · exact h
    · omega
  have hlo' := chordIdx_mem_lower (n := n) (m := m) (by omega)
  have hle_j : j ≤ chordIdx n m :=
    Nat.le_findGreatest (P := fun j => ballVol n j ≤ m) (by omega) hlo
  unfold chord
  rw [ite_eq_right hm0]
  by_cases heq : j = chordIdx n m
  · rw [heq]
  · have hlt_j : j < chordIdx n m := by omega
    have hV1 : ballVol n (j + 1) ≤ ballVol n (chordIdx n m) :=
      ballVol_mono (by omega)
    have hmeq1 : m = ballVol n (j + 1) := by omega
    have hmeq2 : m = ballVol n (chordIdx n m) := by omega
    have hidx_eq : chordIdx n m = j + 1 := by
      by_contra hc
      have hVeq : ballVol n (chordIdx n m) = ballVol n (j + 1) := by omega
      rcases lt_trichotomy (chordIdx n m) (j + 1) with hlt' | heq' | hgt'
      · have hlt'' := ballVol_strictMono (n := n) hlt' (by omega)
        omega
      · exact absurd heq' hc
      · have hlt'' := ballVol_strictMono (n := n) hgt' (chordIdx_le n m)
        omega
    rw [hidx_eq, hmeq1]
    have hnorm : j + 1 + 1 = j + 2 := rfl
    rw [hnorm]
    simp only [sub_self, mul_zero, add_zero]
    exact (chordSlope_cont (n := n) (j := j) (by omega)).symm

private theorem chord_ballVol {n j : ℕ} (hj : j < n) :
    chord n (ballVol n j) = (ballVol n (j + 1) : ℚ) := by
  have hm0 : ballVol n j ≠ 0 := ne_of_gt (ballVol_pos n j)
  have hlt : ballVol n j < 2 ^ n := by
    calc ballVol n j < ballVol n (j + 1) := ballVol_strict_succ (by omega)
      _ ≤ ballVol n n := ballVol_mono (by omega)
      _ = 2 ^ n := ballVol_eq_pow le_rfl
  rw [chord_eq_of_mem hm0 hlt hj le_rfl (ballVol_mono (Nat.le_succ j))]
  simp only [sub_self, mul_zero, add_zero]

private theorem chordSlope_nonneg (n j : ℕ) : 0 ≤ chordSlope n j := by
  unfold chordSlope
  positivity

private theorem chord_nonneg (n m : ℕ) : 0 ≤ chord n m := by
  unfold chord
  split_ifs with h0
  · exact le_rfl
  · have hlo := chordIdx_mem_lower (n := n) (m := m) (by omega)
    have hs := chordSlope_nonneg n (chordIdx n m)
    have hV : (0 : ℚ) ≤ (ballVol n (chordIdx n m + 1) : ℚ) := by positivity
    have hdiff : (0 : ℚ) ≤ (m : ℚ) - (ballVol n (chordIdx n m) : ℚ) := by
      have hle : (ballVol n (chordIdx n m) : ℚ) ≤ (m : ℚ) := by exact_mod_cast hlo
      linarith
    have hmul := mul_nonneg hs hdiff
    linarith

private theorem chord_eq_pow {n m : ℕ} (h : 2 ^ n ≤ m) :
    chord n m = (((2 ^ n : ℕ)) : ℚ) := by
  have hpos : 0 < 2 ^ n := by positivity
  have hm0 : m ≠ 0 := by omega
  have hidx : chordIdx n m = n := by
    unfold chordIdx
    apply Nat.findGreatest_eq
    show ballVol n n ≤ m
    rw [ballVol_eq_pow le_rfl]
    exact h
  unfold chord
  rw [ite_eq_right hm0, hidx]
  have hV1 : ballVol n (n + 1) = 2 ^ n := ballVol_eq_pow (by omega)
  have hVn : ballVol n n = 2 ^ n := ballVol_eq_pow le_rfl
  have hs : chordSlope n n = 0 := by
    unfold chordSlope
    have c1 : n.choose (n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have c2 : n.choose (n + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [c1, c2]
    simp
  rw [hV1, hVn, hs]
  simp

private theorem harperChordBallVolAll (n j : ℕ) :
    chord n (ballVol n j) = (ballVol n (j + 1) : ℚ) := by
  by_cases hj : j < n
  · exact chord_ballVol hj
  · have h1 : ballVol n j = 2 ^ n := ballVol_eq_pow (by omega)
    have h2 : ballVol n (j + 1) = 2 ^ n := ballVol_eq_pow (by omega)
    rw [h1, h2, chord_eq_pow le_rfl]

private theorem chordSlope_eq (n j : ℕ) (h : j + 1 ≤ n) :
    chordSlope n j = (((n - (j + 1) : ℕ)) : ℚ) / ((j + 2 : ℕ) : ℚ) := by
  by_cases h2 : j + 2 ≤ n
  · have hC : (n.choose (j + 1) : ℚ) ≠ 0 := by
      have hpos : 0 < n.choose (j + 1) := Nat.choose_pos (by omega)
      exact_mod_cast ne_of_gt hpos
    have hD : (((j + 2 : ℕ)) : ℚ) ≠ 0 := by
      have hpos : (0 : ℚ) < (((j + 2 : ℕ)) : ℚ) := by
        exact_mod_cast (by omega : 0 < j + 2)
      exact ne_of_gt hpos
    have hkey := Nat.choose_succ_right_eq n (j + 1)
    rw [show j + 1 + 1 = j + 2 from rfl] at hkey
    have hkey' : n.choose (j + 2) * (j + 2)
        = (n - (j + 1)) * n.choose (j + 1) := by
      rw [mul_comm (n - (j + 1)) _]
      exact hkey
    unfold chordSlope
    rw [div_eq_div_iff hC hD]
    exact_mod_cast hkey'
  · have c2 : n.choose (j + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have e0 : n - (j + 1) = 0 := by omega
    unfold chordSlope
    rw [c2, e0]
    simp only [Nat.cast_zero, zero_div]

private theorem choose_pascal_add (n c : ℕ) :
    (n + 1).choose (c + 2) = n.choose (c + 1) + n.choose (c + 2) := by
  have h := Nat.choose_succ_succ' n (c + 1)
  rwa [show c + 1 + 1 = c + 2 from rfl] at h

private theorem ballVol_pascal_pred {n c : ℕ} (hc : 1 ≤ c) :
    ballVol (n + 1) c = ballVol n c + ballVol n (c - 1) := by
  have h := ballVol_pascal n (c - 1)
  have e : c - 1 + 1 = c := by omega
  rwa [e] at h

private theorem chordSlope_caseB {n c : ℕ} (hc1 : 1 ≤ c) (hcn : c + 1 ≤ n) :
    chordSlope (n + 1) c ≤ chordSlope n (c - 1) := by
  have hs1 := chordSlope_eq (n + 1) c (by omega)
  have hs2 := chordSlope_eq n (c - 1) (by omega)
  have e1 : (n + 1) - (c + 1) = n - c := by omega
  have e2 : n - (c - 1 + 1) = n - c := by omega
  have e3 : c - 1 + 2 = c + 1 := by omega
  rw [e1] at hs1
  rw [e2, e3] at hs2
  rw [hs1, hs2]
  have hB1 : (0 : ℚ) < (((c + 1 : ℕ)) : ℚ) := by
    exact_mod_cast (by omega : 0 < c + 1)
  have hB2 : (0 : ℚ) < (((c + 2 : ℕ)) : ℚ) := by
    exact_mod_cast (by omega : 0 < c + 2)
  rw [div_le_div_iff₀ hB2 hB1]
  have hle : (((c + 1 : ℕ)) : ℚ) ≤ (((c + 2 : ℕ)) : ℚ) := by
    exact_mod_cast (by omega : c + 1 ≤ c + 2)
  have hA : (0 : ℚ) ≤ (((n - c : ℕ)) : ℚ) := by positivity
  exact mul_le_mul_of_nonneg_left hle hA

private theorem chordSlope_caseHi {n c : ℕ} (hcn : c + 1 ≤ n) :
    chordSlope n c ≤ chordSlope (n + 1) c := by
  have hs1 := chordSlope_eq n c hcn
  have hs2 := chordSlope_eq (n + 1) c (by omega)
  rw [hs1, hs2]
  have hB : (0 : ℚ) < (((c + 2 : ℕ)) : ℚ) := by
    exact_mod_cast (by omega : 0 < c + 2)
  rw [div_le_div_iff₀ hB hB]
  have hle : n - (c + 1) ≤ (n + 1) - (c + 1) := by omega
  have hleQ : (((n - (c + 1) : ℕ)) : ℚ) ≤ ((((n + 1) - (c + 1) : ℕ)) : ℚ) := by
    exact_mod_cast hle
  exact mul_le_mul_of_nonneg_right hleQ (le_of_lt hB)

private theorem chordIdx_interval {n m : ℕ} (hm0 : m ≠ 0) (hlt : m < 2 ^ n) :
    ∃ c, c < n ∧ ballVol n c ≤ m ∧ m ≤ ballVol n (c + 1) := by
  have hidx : chordIdx n m < n := by
    by_contra hc
    have hle := chordIdx_le n m
    have heq : chordIdx n m = n := by omega
    have hlo' := chordIdx_mem_lower (n := n) (m := m) (by omega)
    rw [heq, ballVol_eq_pow le_rfl] at hlo'
    omega
  refine ⟨chordIdx n m, hidx,
    chordIdx_mem_lower (n := n) (m := m) (by omega), ?_⟩
  rcases chordIdx_mem_upper (n := n) (m := m) with h | h
  · exact Nat.le_of_lt h
  · omega

private theorem choose_logConcave (m k : ℕ) (h : k + 1 ≤ m) :
    (m.choose (k + 2)) * (m.choose k)
      ≤ (m.choose (k + 1)) * (m.choose (k + 1)) := by
  by_cases h2 : k + 2 ≤ m
  · have eA := Nat.choose_succ_right_eq m k
    have eB := Nat.choose_succ_right_eq m (k + 1)
    rw [show k + 1 + 1 = k + 2 from rfl] at eB
    have hsub : m - (k + 1) = m - k - 1 := by omega
    rw [hsub] at eB
    have hX : (0 : ℕ) < (m - k) * (k + 2) :=
      Nat.mul_pos (by omega) (by omega)
    have hY : (k + 1) * (m - k - 1) ≤ (m - k) * (k + 2) := by
      calc (k + 1) * (m - k - 1) ≤ (k + 1) * (m - k) :=
            Nat.mul_le_mul le_rfl (Nat.sub_le _ _)
        _ = (m - k) * (k + 1) := by ring
        _ ≤ (m - k) * (k + 2) := Nat.mul_le_mul le_rfl (by omega)
    have hmul : (m.choose (k + 2) * m.choose k) * ((m - k) * (k + 2))
        = ((m.choose (k + 1) * m.choose (k + 1)))
          * ((k + 1) * (m - k - 1)) := by
      calc (m.choose (k + 2) * m.choose k) * ((m - k) * (k + 2))
          = (m.choose (k + 2) * (k + 2)) * (m.choose k * (m - k)) := by ring
        _ = (m.choose (k + 1) * (m - k - 1)) * (m.choose (k + 1) * (k + 1)) := by
            rw [eB, ← eA]
        _ = ((m.choose (k + 1) * m.choose (k + 1)))
            * ((k + 1) * (m - k - 1)) := by ring
    have hle : (m.choose (k + 2) * m.choose k) * ((m - k) * (k + 2))
        ≤ ((m.choose (k + 1) * m.choose (k + 1))) * ((m - k) * (k + 2)) := by
      rw [hmul]
      exact Nat.mul_le_mul le_rfl hY
    exact le_of_mul_le_mul_right hle hX
  · have hz : m.choose (k + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [hz, zero_mul]
    exact Nat.zero_le _

private theorem chord_le_pow (n m : ℕ) : chord n m ≤ (((2 ^ n : ℕ)) : ℚ) := by
  by_cases h : 2 ^ n ≤ m
  · rw [chord_eq_pow h]
  · by_cases hm0 : m = 0
    · unfold chord
      rw [ite_eq_left hm0]
      positivity
    · have hlt : m < 2 ^ n := Nat.lt_of_not_ge h
      have hidx : chordIdx n m < n := by
        by_contra hc
        have hle := chordIdx_le n m
        have heq : chordIdx n m = n := by omega
        have hlo' := chordIdx_mem_lower (n := n) (m := m) (by omega)
        rw [heq, ballVol_eq_pow le_rfl] at hlo'
        omega
      have hlo := chordIdx_mem_lower (n := n) (m := m) (by omega)
      have hup : m < ballVol n (chordIdx n m + 1) := by
        rcases chordIdx_mem_upper (n := n) (m := m) with h' | h'
        · exact h'
        · omega
      rw [chord_eq_of_mem hm0 hlt hidx hlo (Nat.le_of_lt hup)]
      have hs := chordSlope_nonneg n (chordIdx n m)
      have hmul := chordSlope_mul n (chordIdx n m) (by omega)
      have hdiff : ((m : ℚ) - ballVol n (chordIdx n m) : ℚ)
          ≤ ((ballVol n (chordIdx n m + 1) : ℕ) : ℚ)
            - ballVol n (chordIdx n m) := by
        have hle : (m : ℚ) ≤ (ballVol n (chordIdx n m + 1) : ℚ) := by
          exact_mod_cast Nat.le_of_lt hup
        linarith
      have hC : ((ballVol n (chordIdx n m + 1) : ℕ) : ℚ)
          - (ballVol n (chordIdx n m) : ℕ)
          = (n.choose (chordIdx n m + 1) : ℚ) := by
        have hq : ((ballVol n (chordIdx n m + 1) : ℕ) : ℚ)
            = ((ballVol n (chordIdx n m) : ℕ) : ℚ)
              + (n.choose (chordIdx n m + 1) : ℚ) := by
          exact_mod_cast ballVol_succ n (chordIdx n m)
        linarith
      have hV2 : ballVol n (chordIdx n m + 2) ≤ 2 ^ n := ballVol_le_pow n _
      have hstep : ballVol n (chordIdx n m + 1) + n.choose (chordIdx n m + 2)
          = ballVol n (chordIdx n m + 2) := by
        have h := ballVol_succ n (chordIdx n m + 1)
        rw [show chordIdx n m + 1 + 1 = chordIdx n m + 2 from rfl] at h
        exact h.symm
      have hdiff' : ((m : ℚ) - ballVol n (chordIdx n m) : ℚ)
          ≤ (n.choose (chordIdx n m + 1) : ℚ) := by
        rw [← hC]
        exact hdiff
      have hle : chordSlope n (chordIdx n m) * ((m : ℚ) - ballVol n (chordIdx n m))
          ≤ (n.choose (chordIdx n m + 2) : ℚ) := by
        rw [← hmul]
        exact mul_le_mul_of_nonneg_left hdiff' hs
      have hfin : ((ballVol n (chordIdx n m + 1) : ℕ) : ℚ)
          + (n.choose (chordIdx n m + 2) : ℚ) ≤ (((2 ^ n : ℕ)) : ℚ) := by
        have heq : ((ballVol n (chordIdx n m + 1) : ℕ) : ℚ)
            + (n.choose (chordIdx n m + 2) : ℚ)
            = ((ballVol n (chordIdx n m + 2) : ℕ) : ℚ) := by
          exact_mod_cast hstep
        rw [heq]
        exact_mod_cast hV2
      linarith [hle]

private theorem chord_zero (n : ℕ) : chord n 0 = 0 := by
  unfold chord
  exact ite_eq_left rfl

private theorem chord_mono {n a b : ℕ} (h : a ≤ b) : chord n a ≤ chord n b := by
  by_cases ha0 : a = 0
  · subst ha0
    rw [chord_zero]
    exact chord_nonneg n b
  · by_cases hb : 2 ^ n ≤ b
    · rw [chord_eq_pow hb]
      exact chord_le_pow n a
    · have hblt : b < 2 ^ n := Nat.lt_of_not_ge hb
      have halt : a < 2 ^ n := by omega
      have ha0' : 0 < a := by omega
      have hb0 : 0 < b := by omega
      have hi : chordIdx n a < n := by
        by_contra hc
        have hle := chordIdx_le n a
        have heq : chordIdx n a = n := by omega
        have hlo' := chordIdx_mem_lower (n := n) (m := a) ha0'
        rw [heq, ballVol_eq_pow le_rfl] at hlo'
        omega
      have hj : chordIdx n b < n := by
        by_contra hc
        have hle := chordIdx_le n b
        have heq : chordIdx n b = n := by omega
        have hlo' := chordIdx_mem_lower (n := n) (m := b) hb0
        rw [heq, ballVol_eq_pow le_rfl] at hlo'
        omega
      have hia : ballVol n (chordIdx n a) ≤ a :=
        chordIdx_mem_lower (n := n) (m := a) ha0'
      have hib : ballVol n (chordIdx n b) ≤ b :=
        chordIdx_mem_lower (n := n) (m := b) hb0
      have hua : a < ballVol n (chordIdx n a + 1) := by
        rcases chordIdx_mem_upper (n := n) (m := a) with h' | h'
        · exact h'
        · omega
      have hub : b < ballVol n (chordIdx n b + 1) := by
        rcases chordIdx_mem_upper (n := n) (m := b) with h' | h'
        · exact h'
        · omega
      have hij : chordIdx n a ≤ chordIdx n b := by
        have hmem : ballVol n (chordIdx n a) ≤ b := by omega
        exact Nat.le_findGreatest (P := fun j => ballVol n j ≤ b)
          (chordIdx_le n a) hmem
      rw [chord_eq_of_mem (n := n) (m := a) (j := chordIdx n a)
        ha0 halt hi hia (Nat.le_of_lt hua)]
      rw [chord_eq_of_mem (n := n) (m := b) (j := chordIdx n b)
        (by omega) hblt hj hib (Nat.le_of_lt hub)]
      by_cases heq : chordIdx n a = chordIdx n b
      · rw [heq]
        have hs := chordSlope_nonneg n (chordIdx n b)
        have hle : ((a : ℚ) - ballVol n (chordIdx n b) : ℚ)
            ≤ ((b : ℚ) - ballVol n (chordIdx n b) : ℚ) := by
          have hab : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast h
          linarith
        have hmul := mul_le_mul_of_nonneg_left hle hs
        linarith
      · have hlt_ij : chordIdx n a < chordIdx n b := by omega
        have hs_a := chordSlope_nonneg n (chordIdx n a)
        have hs_b := chordSlope_nonneg n (chordIdx n b)
        have hup_a : (ballVol n (chordIdx n a + 1) : ℚ)
            + chordSlope n (chordIdx n a) * ((a : ℚ) - ballVol n (chordIdx n a))
            ≤ (ballVol n (chordIdx n a + 2) : ℚ) := by
          have hle : ((a : ℚ) - ballVol n (chordIdx n a) : ℚ)
              ≤ ((ballVol n (chordIdx n a + 1) : ℕ) : ℚ)
                - ballVol n (chordIdx n a) := by
            have hab : (a : ℚ) ≤ (ballVol n (chordIdx n a + 1) : ℚ) := by
              exact_mod_cast Nat.le_of_lt hua
            linarith
          have hmul_le : chordSlope n (chordIdx n a)
              * ((a : ℚ) - ballVol n (chordIdx n a))
              ≤ chordSlope n (chordIdx n a)
                * (((ballVol n (chordIdx n a + 1) : ℕ) : ℚ)
                  - ballVol n (chordIdx n a)) :=
            mul_le_mul_of_nonneg_left hle hs_a
          have hcont := chordSlope_cont (n := n) (j := chordIdx n a) (by omega)
          linarith
        have hlo_b : ((ballVol n (chordIdx n b + 1) : ℕ) : ℚ)
            ≤ (ballVol n (chordIdx n b + 1) : ℚ)
              + chordSlope n (chordIdx n b)
                * ((b : ℚ) - ballVol n (chordIdx n b)) := by
          have hdiff : (0 : ℚ) ≤ ((b : ℚ) - ballVol n (chordIdx n b) : ℚ) := by
            have hle : (ballVol n (chordIdx n b) : ℚ) ≤ (b : ℚ) := by
              exact_mod_cast hib
            linarith
          have hmul := mul_nonneg hs_b hdiff
          linarith
        have hVV : (ballVol n (chordIdx n a + 2) : ℚ)
            ≤ (ballVol n (chordIdx n b + 1) : ℚ) := by
          have hmono : ballVol n (chordIdx n a + 2)
              ≤ ballVol n (chordIdx n b + 1) :=
            ballVol_mono (by omega)
          exact_mod_cast hmono
        linarith [hup_a, hlo_b, hVV]

/-- Chord combination across a cube split (Harper induction step inequality). -/
private theorem chord_combine {n u v : ℕ} (hvu : v ≤ u) (hu : u ≤ 2 ^ n) :
    chord n u + max (u : ℚ) (chord n v) ≥ chord (n + 1) (u + v) := by
  by_cases hJ0 : u + v = 0
  · have hu0 : u = 0 := by omega
    have hv0 : v = 0 := by omega
    rw [hu0, hv0, show (0 : ℕ) + 0 = 0 from rfl]
    simp only [chord_zero, Nat.cast_zero, max_self, add_zero, le_refl]
  · by_cases hJcap : 2 ^ (n + 1) ≤ u + v
    · have h2n : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
      have hu2 : u = 2 ^ n := by omega
      have hv2 : v = 2 ^ n := by omega
      have e1 : (2 : ℕ) ^ n + 2 ^ n = 2 ^ (n + 1) := by rw [pow_succ]; ring
      rw [hu2, hv2, e1, chord_eq_pow (n := n + 1) (m := 2 ^ (n + 1)) le_rfl,
        chord_eq_pow (n := n) (m := 2 ^ n) le_rfl]
      have e1q : ((2 ^ n : ℕ) : ℚ) + ((2 ^ n : ℕ) : ℚ)
          = ((2 ^ (n + 1) : ℕ) : ℚ) := by exact_mod_cast e1
      simp only [max_self]
      linarith [e1q]
    · have hJlt : u + v < 2 ^ (n + 1) := Nat.lt_of_not_ge hJcap
      have hJpos : 0 < u + v := by omega
      obtain ⟨c, hc_lt, hc_lo, hc_hi⟩ := chordIdx_interval (n := n + 1) (m := u + v)
        (by omega) hJlt
      by_cases hcn : c = n
      · rw [hcn] at hc_lo hc_hi
        have hUn : ballVol (n + 1) n = 2 ^ (n + 1) - 1 := by
          have h1 := ballVol_eq_pow (n := n + 1) (k := n + 1) le_rfl
          have h2 := ballVol_succ (n + 1) n
          have h3 : (n + 1).choose (n + 1) = 1 := Nat.choose_self _
          omega
        have h2n : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
        have hu2 : u = 2 ^ n := by omega
        rw [hu2, chord_eq_pow (n := n) (m := 2 ^ n) le_rfl]
        have hmax : max ((2 ^ n : ℕ) : ℚ) (chord n v) = ((2 ^ n : ℕ) : ℚ) :=
          max_eq_left (chord_le_pow n v)
        rw [hmax]
        have e1 : (2 : ℕ) ^ n + 2 ^ n = 2 ^ (n + 1) := by rw [pow_succ]; ring
        have e1q : ((2 ^ n : ℕ) : ℚ) + ((2 ^ n : ℕ) : ℚ)
            = ((2 ^ (n + 1) : ℕ) : ℚ) := by exact_mod_cast e1
        rw [e1q]
        exact chord_le_pow (n + 1) (2 ^ n + v)
      · have hcn' : c < n := by omega
        by_cases hB : u < ballVol n c
        · have hc1 : 1 ≤ c := by
            by_contra hc0
            have hc0' : c = 0 := by omega
            rw [hc0'] at hB
            have hW0 := ballVol_zero n
            omega
          have hU := ballVol_pascal n c
          have hUpred := ballVol_pascal_pred (n := n) (c := c) hc1
          have hv_lo : ballVol n (c - 1) < v := by omega
          have ecm1 : c - 1 + 1 = c := by omega
          have ecm2 : c - 1 + 2 = c + 1 := by omega
          have hu_int : ballVol n (c - 1) ≤ u ∧ u ≤ ballVol n c := by
            constructor
            · omega
            · exact Nat.le_of_lt hB
          have hv_int : ballVol n (c - 1) ≤ v ∧ v ≤ ballVol n c := by
            constructor
            · exact Nat.le_of_lt hv_lo
            · omega
          have hu_lt : u < 2 ^ n := by
            calc u < ballVol n c := hB
              _ ≤ ballVol n n := ballVol_mono (by omega)
              _ = 2 ^ n := ballVol_eq_pow le_rfl
          have hv_lt : v < 2 ^ n := by omega
          have hu0 : u ≠ 0 := by omega
          have hv0 : v ≠ 0 := by omega
          have hu_hi : u ≤ ballVol n (c - 1 + 1) := by
            rw [ecm1]
            exact hu_int.2
          have hv_hi : v ≤ ballVol n (c - 1 + 1) := by
            rw [ecm1]
            exact hv_int.2
          have hcu := chord_eq_of_mem (n := n) (m := u) (j := c - 1) hu0 hu_lt
            (by omega) hu_int.1 hu_hi
          rw [ecm1] at hcu
          have hcv := chord_eq_of_mem (n := n) (m := v) (j := c - 1) hv0 hv_lt
            (by omega) hv_int.1 hv_hi
          rw [ecm1] at hcv
          have hmax : max (u : ℚ) (chord n v) = chord n v := by
            apply max_eq_right
            rw [hcv]
            have hs := chordSlope_nonneg n (c - 1)
            have hdiff : (0 : ℚ) ≤ ((v : ℚ) - ballVol n (c - 1)) := by
              have hle : ((ballVol n (c - 1) : ℕ) : ℚ) ≤ (v : ℚ) := by
                exact_mod_cast hv_int.1
              linarith
            have hmul := mul_nonneg hs hdiff
            have huW : (u : ℚ) < ((ballVol n c : ℕ) : ℚ) := by exact_mod_cast hB
            linarith
          have hJU : chord (n + 1) (u + v)
              = (ballVol (n + 1) (c + 1) : ℚ)
                + chordSlope (n + 1) c
                  * ((((u + v : ℕ)) : ℚ) - ballVol (n + 1) c) :=
            chord_eq_of_mem (n := n + 1) (m := u + v) (j := c) (by omega) hJlt
              (by omega) hc_lo hc_hi
          have hJcast : ((((u + v : ℕ))) : ℚ) = (u : ℚ) + (v : ℚ) :=
            Nat.cast_add u v
          have hW1 : ballVol n c = ballVol n (c - 1) + n.choose c := by
            have h := ballVol_succ n (c - 1)
            rwa [ecm1] at h
          have hmul' := chordSlope_mul n (c - 1) (by omega)
          rw [ecm1, ecm2] at hmul'
          have hslope : chordSlope (n + 1) c ≤ chordSlope n (c - 1) :=
            chordSlope_caseB (n := n) (c := c) hc1 (by omega)
          have hUq : ((ballVol (n + 1) (c + 1) : ℕ) : ℚ)
              = ((ballVol n (c + 1) : ℕ) : ℚ) + ((ballVol n c : ℕ) : ℚ) := by
            exact_mod_cast hU
          have hUpredq : ((ballVol (n + 1) c : ℕ) : ℚ)
              = ((ballVol n c : ℕ) : ℚ) + ((ballVol n (c - 1) : ℕ) : ℚ) := by
            exact_mod_cast hUpred
          have hW1q : ((ballVol n c : ℕ) : ℚ)
              = ((ballVol n (c - 1) : ℕ) : ℚ) + ((n.choose c : ℕ) : ℚ) := by
            exact_mod_cast hW1
          have eUc : ((ballVol (n + 1) c : ℕ) : ℚ)
              - 2 * ((ballVol n (c - 1) : ℕ) : ℚ)
              = ((n.choose c : ℕ) : ℚ) := by linarith [hUpredq, hW1q]
          have h0 : 2 * ((ballVol n c : ℕ) : ℚ)
              + chordSlope n (c - 1)
                * (((ballVol (n + 1) c : ℕ) : ℚ)
                  - 2 * ((ballVol n (c - 1) : ℕ) : ℚ))
              = ((ballVol (n + 1) (c + 1) : ℕ) : ℚ) := by
            rw [eUc, hmul']
            have hWc1 : ballVol n (c + 1) = ballVol n c + n.choose (c + 1) :=
              ballVol_succ n c
            have hWc1q : ((ballVol n (c + 1) : ℕ) : ℚ)
                = ((ballVol n c : ℕ) : ℚ) + ((n.choose (c + 1) : ℕ) : ℚ) := by
              exact_mod_cast hWc1
            linarith [hUq, hWc1q]
          have hval' : (chord n u + max (u : ℚ) (chord n v))
              - chord (n + 1) (u + v)
              = (chordSlope n (c - 1) - chordSlope (n + 1) c)
                * ((((u + v : ℕ)) : ℚ) - ((ballVol (n + 1) c : ℕ) : ℚ)) := by
            rw [hcu, hmax, hcv, hJU]
            linear_combination h0 - (chordSlope n (c - 1)) * hJcast
          have hslope_nn : 0 ≤ chordSlope n (c - 1) - chordSlope (n + 1) c := by
            linarith [hslope]
          have hJnn : (0 : ℚ)
              ≤ ((((u + v : ℕ))) : ℚ) - ((ballVol (n + 1) c : ℕ) : ℚ) := by
            have hle : ((ballVol (n + 1) c : ℕ) : ℚ)
                ≤ ((((u + v : ℕ))) : ℚ) := by exact_mod_cast hc_lo
            linarith
          have hprod := mul_nonneg hslope_nn hJnn
          linarith [hval', hprod]
        · by_cases hHi : ballVol n (c + 1) ≤ u
          · have hU := ballVol_pascal n c
            have hvW : v ≤ ballVol n c := by omega
            have hchordv : chord n v ≤ (u : ℚ) := by
              calc chord n v ≤ chord n (ballVol n c) := chord_mono hvW
                _ = (ballVol n (c + 1) : ℚ) := chord_ballVol hcn'
                _ ≤ (u : ℚ) := by exact_mod_cast hHi
            have hmax : max (u : ℚ) (chord n v) = (u : ℚ) := max_eq_left hchordv
            have hchordu : ((ballVol n (c + 2) : ℕ) : ℚ) ≤ chord n u := by
              by_cases hc1 : c + 1 < n
              · have hcb := chord_ballVol (n := n) (j := c + 1) hc1
                have e : c + 1 + 1 = c + 2 := rfl
                rw [e] at hcb
                rw [← hcb]
                exact chord_mono hHi
              · have hcn1 : c + 1 = n := by omega
                have hu2 : u = 2 ^ n := by
                  have hW : ballVol n (c + 1) = 2 ^ n := by
                    rw [hcn1]
                    exact ballVol_eq_pow le_rfl
                  omega
                rw [hu2, chord_eq_pow (n := n) (m := 2 ^ n) le_rfl]
                have hle : ballVol n (c + 2) ≤ 2 ^ n := ballVol_le_pow n _
                exact_mod_cast hle
            have hJU : chord (n + 1) (u + v)
                = (ballVol (n + 1) (c + 1) : ℚ)
                  + chordSlope (n + 1) c
                    * ((((u + v : ℕ)) : ℚ) - ballVol (n + 1) c) :=
              chord_eq_of_mem (n := n + 1) (m := u + v) (j := c) (by omega) hJlt
                (by omega) hc_lo hc_hi
            rw [hJU, hmax]
            have hs := chordSlope_nonneg (n + 1) c
            have hmul := chordSlope_mul (n + 1) c (by omega)
            have hJle : ((((u + v : ℕ)) : ℚ) - ballVol (n + 1) c : ℚ)
                ≤ (((n + 1).choose (c + 1) : ℕ) : ℚ) := by
              have h1 : ((((u + v : ℕ))) : ℚ)
                  ≤ ((ballVol (n + 1) (c + 1) : ℕ) : ℚ) := by
                exact_mod_cast hc_hi
              have h2 : ((ballVol (n + 1) (c + 1) : ℕ) : ℚ)
                  - ((ballVol (n + 1) c : ℕ) : ℚ)
                  = ((((n + 1).choose (c + 1) : ℕ)) : ℚ) := by
                have hq : ((ballVol (n + 1) (c + 1) : ℕ) : ℚ)
                    = ((ballVol (n + 1) c : ℕ) : ℚ)
                      + ((((n + 1).choose (c + 1) : ℕ)) : ℚ) := by
                  exact_mod_cast ballVol_succ (n + 1) c
                linarith
              linarith
            have hsJ : chordSlope (n + 1) c
                * ((((u + v : ℕ)) : ℚ) - ballVol (n + 1) c)
                ≤ ((((n + 1).choose (c + 2) : ℕ)) : ℚ) := by
              rw [← hmul]
              exact mul_le_mul_of_nonneg_left hJle hs
            have hW2 : ballVol n (c + 2)
                = ballVol n (c + 1) + n.choose (c + 2) := by
              have h := ballVol_succ n (c + 1)
              rwa [show c + 1 + 1 = c + 2 from rfl] at h
            have hW1 : ballVol n (c + 1) = ballVol n c + n.choose (c + 1) :=
              ballVol_succ n c
            have hpas := choose_pascal_add n c
            have hUq : ((ballVol (n + 1) (c + 1) : ℕ) : ℚ)
                = ((ballVol n (c + 1) : ℕ) : ℚ)
                  + ((ballVol n c : ℕ) : ℚ) := by exact_mod_cast hU
            have hW2q : ((ballVol n (c + 2) : ℕ) : ℚ)
                = ((ballVol n (c + 1) : ℕ) : ℚ)
                  + ((n.choose (c + 2) : ℕ) : ℚ) := by exact_mod_cast hW2
            have hW1q : ((ballVol n (c + 1) : ℕ) : ℚ)
                = ((ballVol n c : ℕ) : ℚ) + ((n.choose (c + 1) : ℕ) : ℚ) := by
              exact_mod_cast hW1
            have hpasq : ((((n + 1).choose (c + 2)) : ℕ) : ℚ)
                = (((n.choose (c + 1)) : ℕ) : ℚ)
                  + (((n.choose (c + 2)) : ℕ) : ℚ) := by exact_mod_cast hpas
            have huW : ((ballVol n (c + 1) : ℕ) : ℚ) ≤ (u : ℚ) := by
              exact_mod_cast hHi
            linarith [hchordu, hsJ, hUq, hW2q, hW1q, hpasq, huW]
          · have h1 : ballVol n c ≤ u := Nat.le_of_not_gt hB
            have h2 : u < ballVol n (c + 1) := not_le.mp hHi
            by_cases hvC : v ≤ ballVol n c
            · by_cases hc0 : c = 0
              · subst hc0
                have hW0v : ballVol n 0 = 1 := ballVol_zero n
                have hU0v : ballVol (n + 1) 0 = 1 := ballVol_zero (n + 1)
                have hW1v : ballVol n 1 = n + 1 := by
                  have h := ballVol_succ n 0
                  have e01 : (0 : ℕ) + 1 = 1 := by omega
                  rw [e01, ballVol_zero, Nat.choose_one_right] at h
                  omega
                have hU1v : ballVol (n + 1) 1 = n + 2 := by
                  have h := ballVol_succ (n + 1) 0
                  have e01 : (0 : ℕ) + 1 = 1 := by omega
                  rw [e01, ballVol_zero, Nat.choose_one_right] at h
                  omega
                have hn1 : 1 ≤ n := hcn'
                have hu_lt : u < 2 ^ n := by
                  calc u < ballVol n 1 := h2
                    _ ≤ ballVol n n := ballVol_mono (by omega)
                    _ = 2 ^ n := ballVol_eq_pow le_rfl
                have hu0 : u ≠ 0 := by omega
                have hcu : chord n u = (ballVol n 1 : ℚ)
                    + chordSlope n 0 * (((u : ℕ) : ℚ) - ballVol n 0) :=
                  chord_eq_of_mem (n := n) (m := u) (j := 0) hu0 hu_lt
                    (by omega) (by omega) (Nat.le_of_lt h2)
                have hJU : chord (n + 1) (u + v)
                    = (ballVol (n + 1) 1 : ℚ)
                      + chordSlope (n + 1) 0
                        * ((((u + v : ℕ)) : ℚ) - ballVol (n + 1) 0) :=
                  chord_eq_of_mem (n := n + 1) (m := u + v) (j := 0) (by omega)
                    hJlt (by omega) hc_lo hc_hi
                have hJcast : ((((u + v : ℕ))) : ℚ) = (u : ℚ) + (v : ℚ) :=
                  Nat.cast_add u v
                have seq1 := chordSlope_eq n 0 hn1
                have seq2 := chordSlope_eq (n + 1) 0 (by omega)
                have i1 : n - (0 + 1) = n - 1 := by omega
                have i2 : (0 : ℕ) + 2 = 2 := by omega
                have i3 : (n + 1) - (0 + 1) = n := by omega
                rw [i1, i2] at seq1
                rw [i3, i2] at seq2
                have hW1q : ((ballVol n 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by
                  exact_mod_cast hW1v
                have hU1q : ((ballVol (n + 1) 1 : ℕ) : ℚ) = (n : ℚ) + 2 := by
                  exact_mod_cast hU1v
                have hW0q : ((ballVol n 0 : ℕ) : ℚ) = 1 := by
                  exact_mod_cast hW0v
                have hU0q : ((ballVol (n + 1) 0 : ℕ) : ℚ) = 1 := by
                  exact_mod_cast hU0v
                rcases Nat.eq_zero_or_pos v with rfl | hpos
                · have hch0 : chord n 0 = 0 := chord_zero n
                  have hmax0 : max (u : ℚ) (chord n 0) = (u : ℚ) := by
                    rw [hch0]
                    exact max_eq_left (by positivity)
                  have hJu : chord (n + 1) u = (ballVol (n + 1) 1 : ℚ)
                      + chordSlope (n + 1) 0
                        * (((u : ℕ) : ℚ) - ballVol (n + 1) 0) :=
                    chord_eq_of_mem (n := n + 1) (m := u) (j := 0) hu0
                      (by
                        have h2' : (2 : ℕ) ^ n < 2 ^ (n + 1) := by
                          have hpos' : 0 < 2 ^ n := by positivity
                          rw [pow_succ]
                          omega
                        omega)
                      (by omega) (by omega) (by omega)
                  rw [hcu, hmax0, add_zero, hJu, seq1, seq2, hW1q, hU1q, hW0q,
                    hU0q]
                  have hu1 : (1 : ℚ) ≤ (u : ℚ) := by
                    have h1' : 1 ≤ u := by omega
                    exact_mod_cast h1'
                  have hnm1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
                    rw [Nat.cast_sub (by omega : 1 ≤ n)]
                    simp
                  nlinarith [hu1, hnm1]
                · have hv1 : v = 1 := by omega
                  subst hv1
                  have hch1 : chord n 1 = ((ballVol n 1 : ℕ) : ℚ) := by
                    have hcb := chord_ballVol (n := n) (j := 0) (by omega)
                    rw [hW0v] at hcb
                    exact hcb
                  have hmax1 : max (u : ℚ) (chord n 1)
                      = ((ballVol n 1 : ℕ) : ℚ) := by
                    rw [hch1]
                    exact max_eq_right (by exact_mod_cast Nat.le_of_lt h2)
                  have hJ1 : chord (n + 1) (u + 1)
                      = (ballVol (n + 1) 1 : ℚ)
                        + chordSlope (n + 1) 0
                          * ((((u + 1 : ℕ)) : ℚ) - ballVol (n + 1) 0) := by
                    apply chord_eq_of_mem (n := n + 1) (m := u + 1) (j := 0)
                    · omega
                    · have h1 : u + 1 ≤ 2 ^ n := by omega
                      have h2' : (2 : ℕ) ^ n < 2 ^ (n + 1) := by
                        have hpos' : 0 < 2 ^ n := by positivity
                        rw [pow_succ]
                        omega
                      omega
                    · omega
                    · omega
                    · omega
                  have hJc : ((((u + 1 : ℕ))) : ℚ) = (u : ℚ) + 1 := by
                    rw [Nat.cast_add, Nat.cast_one]
                  rw [hcu, hmax1, hJ1, seq1, seq2, hW1q, hU1q, hW0q, hU0q, hJc]
                  have huW1 : (u : ℚ) ≤ (n : ℚ) + 1 := by
                    have hW1v' : ballVol n (0 + 1) = n + 1 := hW1v
                    have hle : u ≤ n + 1 := by omega
                    exact_mod_cast hle
                  have hnm1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
                    rw [Nat.cast_sub (by omega : 1 ≤ n)]
                    simp
                  nlinarith [huW1, hnm1]
              · have hc1 : 1 ≤ c := by omega
                have hU := ballVol_pascal n c
                have hUpred := ballVol_pascal_pred (n := n) (c := c) hc1
                have ecm1 : c - 1 + 1 = c := by omega
                have ecm2 : c - 1 + 2 = c + 1 := by omega
                have hu_lt : u < 2 ^ n := by
                  calc u < ballVol n (c + 1) := h2
                    _ ≤ ballVol n n := ballVol_mono (by omega)
                    _ = 2 ^ n := ballVol_eq_pow le_rfl
                have hu0 : u ≠ 0 := by
                  have hWpos := ballVol_pos n c
                  omega
                have hcu : chord n u = (ballVol n (c + 1) : ℚ)
                    + chordSlope n c * (((u : ℕ) : ℚ) - ballVol n c) :=
                  chord_eq_of_mem (n := n) (m := u) (j := c) hu0 hu_lt hcn'
                    h1 (Nat.le_of_lt h2)
                have hJU : chord (n + 1) (u + v)
                    = (ballVol (n + 1) (c + 1) : ℚ)
                      + chordSlope (n + 1) c
                        * ((((u + v : ℕ)) : ℚ) - ballVol (n + 1) c) :=
                  chord_eq_of_mem (n := n + 1) (m := u + v) (j := c) (by omega)
                    hJlt (by omega) hc_lo hc_hi
                have hJcast : ((((u + v : ℕ))) : ℚ) = (u : ℚ) + (v : ℚ) :=
                  Nat.cast_add u v
                have hs1 := chordSlope_eq n c (by omega)
                have hs2 := chordSlope_eq n (c - 1) (by omega)
                have hsU := chordSlope_eq (n + 1) c (by omega)
                have eN : (n + 1) - (c + 1) = n - c := by omega
                rw [ecm1, ecm2] at hs2
                rw [eN] at hsU
                have hsub1 : ((n - (c + 1) : ℕ) : ℚ)
                    = (n : ℚ) - (c : ℚ) - 1 := by
                  have hle : c + 1 ≤ n := by omega
                  have h1x : ((n - (c + 1) : ℕ) : ℚ)
                      = (n : ℚ) - ((c + 1 : ℕ) : ℚ) := by
                    rw [Nat.cast_sub hle]
                  rw [h1x]
                  push_cast
                  ring
                have hsub2 : ((n - c : ℕ) : ℚ) = (n : ℚ) - (c : ℚ) := by
                  have hle : c ≤ n := by omega
                  rw [Nat.cast_sub hle]
                have d1ne : ((c + 1 : ℕ) : ℚ) ≠ 0 := by
                  have hpos : (0 : ℚ) < ((c + 1 : ℕ) : ℚ) := by
                    exact_mod_cast (by omega : 0 < c + 1)
                  exact ne_of_gt hpos
                have d2ne : ((c + 2 : ℕ) : ℚ) ≠ 0 := by
                  have hpos : (0 : ℚ) < ((c + 2 : ℕ) : ℚ) := by
                    exact_mod_cast (by omega : 0 < c + 2)
                  exact ne_of_gt hpos
                have hkey : (chordSlope n c + 1 - chordSlope (n + 1) c)
                    * chordSlope n (c - 1) = chordSlope (n + 1) c := by
                  rw [hs1, hs2, hsU, hsub1, hsub2]
                  field_simp
                  push_cast
                  ring
                have hnn1 : 0 ≤ chordSlope n c + 1 - chordSlope (n + 1) c := by
                  have hexpr : chordSlope n c + 1 - chordSlope (n + 1) c
                      = ((c + 1 : ℕ) : ℚ) / ((c + 2 : ℕ) : ℚ) := by
                    rw [hs1, hsU, hsub1, hsub2]
                    field_simp
                    push_cast
                    ring
                  rw [hexpr]
                  positivity
                have hsle : chordSlope n c ≤ chordSlope (n + 1) c :=
                  chordSlope_caseHi (n := n) (c := c) (by omega)
                have hUq : ((ballVol (n + 1) (c + 1) : ℕ) : ℚ)
                    = ((ballVol n (c + 1) : ℕ) : ℚ)
                      + ((ballVol n c : ℕ) : ℚ) := by
                  exact_mod_cast hU
                have hUpredq : ((ballVol (n + 1) c : ℕ) : ℚ)
                    = ((ballVol n c : ℕ) : ℚ)
                      + ((ballVol n (c - 1) : ℕ) : ℚ) := by
                  exact_mod_cast hUpred
                by_cases hvLow : v ≤ ballVol n (c - 1)
                · have hmax_ge : (u : ℚ) ≤ max (u : ℚ) (chord n v) :=
                    le_max_left _ _
                  have hA : (0 : ℚ)
                      ≤ (u : ℚ) - ((ballVol n c : ℕ) : ℚ) := by
                    have hle : ((ballVol n c : ℕ) : ℚ) ≤ (u : ℚ) := by
                      exact_mod_cast h1
                    linarith
                  have hB : (v : ℚ) - ((ballVol n (c - 1) : ℕ) : ℚ) ≤ 0 := by
                    have hle : (v : ℚ)
                        ≤ ((ballVol n (c - 1) : ℕ) : ℚ) := by
                      exact_mod_cast hvLow
                    linarith
                  have hsU_nn := chordSlope_nonneg (n + 1) c
                  have hleJV : ((((u + v : ℕ))) : ℚ)
                      - ((ballVol (n + 1) c : ℕ) : ℚ)
                      ≤ (u : ℚ) - ((ballVol n c : ℕ) : ℚ) := by
                    linarith [hJcast, hUpredq, hB]
                  have hle1 : chordSlope (n + 1) c
                      * ((((u + v : ℕ)) : ℚ)
                        - ((ballVol (n + 1) c : ℕ) : ℚ))
                      ≤ chordSlope (n + 1) c
                        * ((u : ℚ) - ((ballVol n c : ℕ) : ℚ)) :=
                    mul_le_mul_of_nonneg_left hleJV hsU_nn
                  have hle2 : chordSlope (n + 1) c
                      * ((u : ℚ) - ((ballVol n c : ℕ) : ℚ))
                      ≤ (chordSlope n c + 1)
                        * ((u : ℚ) - ((ballVol n c : ℕ) : ℚ)) :=
                    mul_le_mul_of_nonneg_right (by linarith [hnn1]) hA
                  have hexpand : (chordSlope n c + 1)
                      * ((u : ℚ) - ((ballVol n c : ℕ) : ℚ))
                      = chordSlope n c * ((u : ℚ)
                        - ((ballVol n c : ℕ) : ℚ))
                        + ((u : ℚ) - ((ballVol n c : ℕ) : ℚ)) := by
                    ring
                  have hmono_max : chord n u + (u : ℚ)
                      ≤ chord n u + max (u : ℚ) (chord n v) := by
                    linarith [hmax_ge]
                  have hstep : chord (n + 1) (u + v)
                      ≤ chord n u + (u : ℚ) := by
                    rw [hcu, hJU]
                    linarith [hle1, hle2, hexpand, hUq]
                  exact le_trans hstep hmono_max
                · have hv_ge : ballVol n (c - 1) ≤ v := by omega
                  have hv_lt : v < 2 ^ n := by
                    calc v ≤ ballVol n c := hvC
                      _ < ballVol n (c + 1) :=
                        ballVol_strict_succ (by omega)
                      _ ≤ ballVol n n := ballVol_mono (by omega)
                      _ = 2 ^ n := ballVol_eq_pow le_rfl
                  have hv0 : v ≠ 0 := by
                    have hWpos := ballVol_pos n (c - 1)
                    omega
                  have hv_hi : v ≤ ballVol n (c - 1 + 1) := by
                    rw [ecm1]
                    exact hvC
                  have hcv : chord n v = (ballVol n c : ℚ)
                      + chordSlope n (c - 1)
                        * (((v : ℕ) : ℚ) - ballVol n (c - 1)) := by
                    have h := chord_eq_of_mem (n := n) (m := v) (j := c - 1)
                      hv0 hv_lt (by omega) hv_ge hv_hi
                    rwa [ecm1] at h
                  have hDecomp : ((((u + v : ℕ))) : ℚ)
                      - ((ballVol (n + 1) c : ℕ) : ℚ)
                      = ((u : ℚ) - ((ballVol n c : ℕ) : ℚ))
                        + ((v : ℚ)
                          - ((ballVol n (c - 1) : ℕ) : ℚ)) := by
                    linarith [hJcast, hUpredq]
                  by_cases hmax : (u : ℚ) ≤ chord n v
                  · have hmax_eq : max (u : ℚ) (chord n v)
                        = chord n v := max_eq_right hmax
                    have hA_le : (u : ℚ) - ((ballVol n c : ℕ) : ℚ)
                        ≤ chordSlope n (c - 1)
                          * ((v : ℚ)
                            - ((ballVol n (c - 1) : ℕ) : ℚ)) := by
                      linarith [hmax, hcv]
                    have hkey2 : (chordSlope (n + 1) c - chordSlope n c)
                        * chordSlope n (c - 1)
                        = chordSlope n (c - 1)
                          - chordSlope (n + 1) c := by
                      linear_combination -hkey
                    have hnn2 : (0 : ℚ)
                        ≤ chordSlope (n + 1) c - chordSlope n c := by
                      linarith [hsle]
                    have hmul_le : (chordSlope (n + 1) c - chordSlope n c)
                        * ((u : ℚ) - ((ballVol n c : ℕ) : ℚ))
                        ≤ (chordSlope (n + 1) c - chordSlope n c)
                          * (chordSlope n (c - 1)
                            * ((v : ℚ)
                              - ((ballVol n (c - 1) : ℕ) : ℚ))) :=
                      mul_le_mul_of_nonneg_left hA_le hnn2
                    have hmul_eq : (chordSlope (n + 1) c - chordSlope n c)
                        * (chordSlope n (c - 1)
                          * ((v : ℚ)
                            - ((ballVol n (c - 1) : ℕ) : ℚ)))
                        = (chordSlope n (c - 1)
                          - chordSlope (n + 1) c)
                          * ((v : ℚ)
                            - ((ballVol n (c - 1) : ℕ) : ℚ)) := by
                      rw [← mul_assoc, hkey2]
                    have hex1 : (chordSlope (n + 1) c - chordSlope n c)
                        * ((u : ℚ) - ((ballVol n c : ℕ) : ℚ))
                        = chordSlope (n + 1) c
                          * ((u : ℚ) - ((ballVol n c : ℕ) : ℚ))
                          - chordSlope n c
                            * ((u : ℚ)
                              - ((ballVol n c : ℕ) : ℚ)) := by
                      ring
                    have hex2 : (chordSlope n (c - 1)
                        - chordSlope (n + 1) c)
                        * ((v : ℚ) - ((ballVol n (c - 1) : ℕ) : ℚ))
                        = chordSlope n (c - 1)
                          * ((v : ℚ)
                            - ((ballVol n (c - 1) : ℕ) : ℚ))
                          - chordSlope (n + 1) c
                            * ((v : ℚ)
                              - ((ballVol n (c - 1) : ℕ) : ℚ)) := by
                      ring
                    have hdist : chordSlope (n + 1) c
                        * (((u : ℚ) - ((ballVol n c : ℕ) : ℚ))
                          + ((v : ℚ)
                            - ((ballVol n (c - 1) : ℕ) : ℚ)))
                        = chordSlope (n + 1) c
                          * ((u : ℚ) - ((ballVol n c : ℕ) : ℚ))
                          + chordSlope (n + 1) c
                            * ((v : ℚ)
                              - ((ballVol n (c - 1) : ℕ) : ℚ)) := by
                      ring
                    rw [hcu, hmax_eq, hcv, hJU, hDecomp, hdist]
                    linarith [hmul_le, hmul_eq, hex1, hex2, hUq]
                  · have hlt : chord n v < (u : ℚ) := not_le.mp hmax
                    have hle : chord n v ≤ (u : ℚ) := le_of_lt hlt
                    have hmax_eq : max (u : ℚ) (chord n v)
                        = (u : ℚ) := max_eq_left hle
                    have hge : chordSlope n (c - 1)
                        * ((v : ℚ)
                          - ((ballVol n (c - 1) : ℕ) : ℚ))
                        ≤ (u : ℚ) - ((ballVol n c : ℕ) : ℚ) := by
                      linarith [hle, hcv]
                    have hmul_le : (chordSlope n c + 1
                        - chordSlope (n + 1) c)
                        * (chordSlope n (c - 1)
                          * ((v : ℚ)
                            - ((ballVol n (c - 1) : ℕ) : ℚ)))
                        ≤ (chordSlope n c + 1
                          - chordSlope (n + 1) c)
                          * ((u : ℚ)
                            - ((ballVol n c : ℕ) : ℚ)) :=
                      mul_le_mul_of_nonneg_left hge hnn1
                    have hmul_eq : (chordSlope n c + 1
                        - chordSlope (n + 1) c)
                        * (chordSlope n (c - 1)
                          * ((v : ℚ)
                            - ((ballVol n (c - 1) : ℕ) : ℚ)))
                        = chordSlope (n + 1) c
                          * ((v : ℚ)
                            - ((ballVol n (c - 1) : ℕ) : ℚ)) := by
                      rw [← mul_assoc, hkey]
                    have hex1 : (chordSlope n c + 1
                        - chordSlope (n + 1) c)
                        * ((u : ℚ) - ((ballVol n c : ℕ) : ℚ))
                        = chordSlope n c
                          * ((u : ℚ) - ((ballVol n c : ℕ) : ℚ))
                          + ((u : ℚ) - ((ballVol n c : ℕ) : ℚ))
                          - chordSlope (n + 1) c
                            * ((u : ℚ)
                              - ((ballVol n c : ℕ) : ℚ)) := by
                      ring
                    have hdist : chordSlope (n + 1) c
                        * (((u : ℚ) - ((ballVol n c : ℕ) : ℚ))
                          + ((v : ℚ)
                            - ((ballVol n (c - 1) : ℕ) : ℚ)))
                        = chordSlope (n + 1) c
                          * ((u : ℚ) - ((ballVol n c : ℕ) : ℚ))
                          + chordSlope (n + 1) c
                            * ((v : ℚ)
                              - ((ballVol n (c - 1) : ℕ) : ℚ)) := by
                      ring
                    rw [hcu, hmax_eq, hJU, hDecomp, hdist]
                    linarith [hmul_le, hmul_eq, hex1, hUq]
            · have hv' : ballVol n c < v := not_le.mp hvC
              have hu_lt : u < 2 ^ n := by
                calc u < ballVol n (c + 1) := h2
                  _ ≤ ballVol n n := ballVol_mono (by omega)
                  _ = 2 ^ n := ballVol_eq_pow le_rfl
              have hv_lt : v < 2 ^ n := by omega
              have hu0 : u ≠ 0 := by
                have hWpos := ballVol_pos n c
                omega
              have hv0 : v ≠ 0 := by
                have hWpos := ballVol_pos n c
                omega
              have hcu : chord n u = (ballVol n (c + 1) : ℚ)
                  + chordSlope n c * (((u : ℕ) : ℚ) - ballVol n c) :=
                chord_eq_of_mem (n := n) (m := u) (j := c) hu0 hu_lt hcn'
                  h1 (Nat.le_of_lt h2)
              have hcv : chord n v = (ballVol n (c + 1) : ℚ)
                  + chordSlope n c * (((v : ℕ) : ℚ) - ballVol n c) :=
                chord_eq_of_mem (n := n) (m := v) (j := c) hv0 hv_lt hcn'
                  (Nat.le_of_lt hv') (by omega)
              have hmax : max (u : ℚ) (chord n v) = chord n v := by
                apply max_eq_right
                rw [hcv]
                have hs := chordSlope_nonneg n c
                have hdiff : (0 : ℚ) ≤ ((v : ℚ) - ballVol n c) := by
                  have hle : ((ballVol n c : ℕ) : ℚ) ≤ (v : ℚ) := by
                    exact_mod_cast Nat.le_of_lt hv'
                  linarith
                have hmul := mul_nonneg hs hdiff
                have huW : (u : ℚ) ≤ ((ballVol n (c + 1) : ℕ) : ℚ) := by
                  exact_mod_cast Nat.le_of_lt h2
                linarith
              have hJU : chord (n + 1) (u + v)
                  = (ballVol (n + 1) (c + 1) : ℚ)
                    + chordSlope (n + 1) c
                      * ((((u + v : ℕ)) : ℚ) - ballVol (n + 1) c) :=
                chord_eq_of_mem (n := n + 1) (m := u + v) (j := c) (by omega)
                  hJlt (by omega) hc_lo hc_hi
              have hJcast : ((((u + v : ℕ))) : ℚ) = (u : ℚ) + (v : ℚ) :=
                Nat.cast_add u v
              have hU := ballVol_pascal n c
              have hW1 : ballVol n (c + 1) = ballVol n c + n.choose (c + 1) :=
                ballVol_succ n c
              have hU2 : ballVol (n + 1) (c + 1)
                  = ballVol (n + 1) c + (n + 1).choose (c + 1) :=
                ballVol_succ (n + 1) c
              have hmul1 := chordSlope_mul n c (by omega)
              have hmul2 := chordSlope_mul (n + 1) c (by omega)
              have hpas := choose_pascal_add n c
              have hslope : chordSlope n c ≤ chordSlope (n + 1) c :=
                chordSlope_caseHi (n := n) (c := c) (by omega)
              have hUq : ((ballVol (n + 1) (c + 1) : ℕ) : ℚ)
                  = ((ballVol n (c + 1) : ℕ) : ℚ)
                    + ((ballVol n c : ℕ) : ℚ) := by exact_mod_cast hU
              have hW1q : ((ballVol n (c + 1) : ℕ) : ℚ)
                  = ((ballVol n c : ℕ) : ℚ) + ((n.choose (c + 1) : ℕ) : ℚ) := by
                exact_mod_cast hW1
              have hU2q : ((ballVol (n + 1) (c + 1) : ℕ) : ℚ)
                  = ((ballVol (n + 1) c : ℕ) : ℚ)
                    + ((((n + 1).choose (c + 1) : ℕ)) : ℚ) := by
                exact_mod_cast hU2
              have hpasq : ((((n + 1).choose (c + 2)) : ℕ) : ℚ)
                  = (((n.choose (c + 1)) : ℕ) : ℚ)
                    + (((n.choose (c + 2)) : ℕ) : ℚ) := by exact_mod_cast hpas
              have eA : ((ballVol (n + 1) (c + 1) : ℕ) : ℚ)
                  - 2 * ((ballVol n c : ℕ) : ℚ)
                  = ((n.choose (c + 1) : ℕ) : ℚ) := by linarith [hUq, hW1q]
              have eB : ((ballVol (n + 1) (c + 1) : ℕ) : ℚ)
                  - ((ballVol (n + 1) c : ℕ) : ℚ)
                  = ((((n + 1).choose (c + 1) : ℕ)) : ℚ) := by
                linarith [hU2q]
              have h0' : 2 * ((ballVol n (c + 1) : ℕ) : ℚ)
                  + chordSlope n c
                    * (((ballVol (n + 1) (c + 1) : ℕ) : ℚ)
                      - 2 * ((ballVol n c : ℕ) : ℚ))
                  = ((ballVol (n + 1) (c + 1) : ℕ) : ℚ)
                    + chordSlope (n + 1) c
                      * (((ballVol (n + 1) (c + 1) : ℕ) : ℚ)
                        - ((ballVol (n + 1) c : ℕ) : ℚ)) := by
                rw [eA, eB, hmul1, hmul2]
                linarith [hUq, hW1q, hpasq]
              have hval' : (chord n u + max (u : ℚ) (chord n v))
                  - chord (n + 1) (u + v)
                  = (chordSlope n c - chordSlope (n + 1) c)
                    * ((((u + v : ℕ)) : ℚ)
                      - ((ballVol (n + 1) (c + 1) : ℕ) : ℚ)) := by
                rw [hcu, hmax, hcv, hJU]
                linear_combination h0' - (chordSlope n c) * hJcast
              have hslope_nn : chordSlope n c - chordSlope (n + 1) c ≤ 0 := by
                linarith [hslope]
              have hJnn : ((((u + v : ℕ))) : ℚ)
                  - ((ballVol (n + 1) (c + 1) : ℕ) : ℚ) ≤ 0 := by
                have hle : ((((u + v : ℕ))) : ℚ)
                    ≤ ((ballVol (n + 1) (c + 1) : ℕ) : ℚ) := by
                  exact_mod_cast hc_hi
                linarith
              have hprod := mul_nonneg_of_nonpos_of_nonpos hslope_nn hJnn
              linarith [hval', hprod]

private theorem harperHammingDistCons {β : Type*} [DecidableEq β] (n : ℕ) (a b : β)
    (x y : Fin n → β) :
    hammingDist (Fin.cons (α := fun _ => β) a x) (Fin.cons (α := fun _ => β) b y)
      = hammingDist x y + (if a = b then 0 else 1) := by
  have e1 : (Finset.univ.filter fun i => Fin.cons (α := fun _ => β) a x i
      ≠ Fin.cons (α := fun _ => β) b y i).card
      = ∑ i : Fin (n + 1), (if Fin.cons (α := fun _ => β) a x i
        ≠ Fin.cons (α := fun _ => β) b y i then (1 : ℕ) else 0) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have e2 : (Finset.univ.filter fun i => x i ≠ y i).card
      = ∑ i : Fin n, (if x i ≠ y i then (1 : ℕ) else 0) := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [hammingDist_eq_filter_card]
  rw [e1, e2, Fin.sum_univ_succ]
  have htail : (∑ i : Fin n, (if Fin.cons (α := fun _ => β) a x i.succ
      ≠ Fin.cons (α := fun _ => β) b y i.succ then 1 else 0))
      = ∑ i : Fin n, (if x i ≠ y i then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.cons_succ]
  have hhead : (if Fin.cons (α := fun _ => β) a x 0
      ≠ Fin.cons (α := fun _ => β) b y 0 then (1 : ℕ) else 0)
      = (if a = b then 0 else 1) := by
    simp only [Fin.cons_zero]
    by_cases hab : a = b <;> simp [hab]
  rw [htail, hhead, add_comm]

private theorem harperHammingDistConsEq {β : Type*} [DecidableEq β] (n : ℕ) (a : β)
    (x y : Fin n → β) :
    hammingDist (Fin.cons (α := fun _ => β) a x)
      (Fin.cons (α := fun _ => β) a y) = hammingDist x y := by
  rw [harperHammingDistCons]
  simp

private theorem harperHammingDistConsLe {β : Type*} [DecidableEq β] (n : ℕ) (a b : β)
    (x : Fin n → β) :
    hammingDist (Fin.cons (α := fun _ => β) a x)
      (Fin.cons (α := fun _ => β) b x) ≤ 1 := by
  rw [harperHammingDistCons, hammingDist_self, zero_add]
  by_cases hab : a = b <;> simp [hab]

private def harperConsEmb (n : ℕ) (b : Bool) :
    (Fin n → Bool) ↪ (Fin (n + 1) → Bool) :=
  ⟨Fin.cons (α := fun _ => Bool) b,
    Fin.cons_right_injective (α := fun _ => Bool) b⟩

private theorem harperConsEmbApply (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    harperConsEmb n b y = Fin.cons (α := fun _ => Bool) b y := rfl

private def harperCubeSlice (n : ℕ) (A : Finset (Fin (n + 1) → Bool)) (b : Bool) :
    Finset (Fin n → Bool) :=
  Finset.univ.filter fun y => Fin.cons (α := fun _ => Bool) b y ∈ A

private theorem harperCubeSliceMem (n : ℕ) (A : Finset (Fin (n + 1) → Bool))
    (b : Bool) (y : Fin n → Bool) :
    y ∈ harperCubeSlice n A b ↔ Fin.cons (α := fun _ => Bool) b y ∈ A := by
  simp only [harperCubeSlice, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem harperCardSliceLe (n : ℕ) (A : Finset (Fin (n + 1) → Bool))
    (b : Bool) :
    (harperCubeSlice n A b).card ≤ 2 ^ n := by
  calc (harperCubeSlice n A b).card ≤ Fintype.card (Fin n → Bool) :=
        Finset.card_le_univ _
    _ = 2 ^ n := by rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

private theorem harperCardSliceAdd (n : ℕ) (A : Finset (Fin (n + 1) → Bool)) :
    A.card = (harperCubeSlice n A false).card
      + (harperCubeSlice n A true).card := by
  have hA : A = (harperCubeSlice n A false).map (harperConsEmb n false) ∪
      (harperCubeSlice n A true).map (harperConsEmb n true) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_map, harperConsEmbApply]
    constructor
    · intro hz
      match hz0 : z 0 with
      | false =>
        left
        have hdecomp : z = Fin.cons (α := fun _ => Bool) false
            (Fin.tail (α := fun _ => Bool) z) := by
          have h := (Fin.cons_self_tail z).symm
          rwa [hz0] at h
        refine ⟨Fin.tail (α := fun _ => Bool) z, ?_, hdecomp.symm⟩
        rw [harperCubeSliceMem, ← hdecomp]
        exact hz
      | true =>
        right
        have hdecomp : z = Fin.cons (α := fun _ => Bool) true
            (Fin.tail (α := fun _ => Bool) z) := by
          have h := (Fin.cons_self_tail z).symm
          rwa [hz0] at h
        refine ⟨Fin.tail (α := fun _ => Bool) z, ?_, hdecomp.symm⟩
        rw [harperCubeSliceMem, ← hdecomp]
        exact hz
    · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
      · rw [harperCubeSliceMem] at hy
        exact hy
      · rw [harperCubeSliceMem] at hy
        exact hy
  have hdisj : Disjoint
      ((harperCubeSlice n A false).map (harperConsEmb n false))
      ((harperCubeSlice n A true).map (harperConsEmb n true)) := by
    rw [Finset.disjoint_left]
    intro z hz0 hz1
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hz0
    obtain ⟨y', _, heq⟩ := Finset.mem_map.mp hz1
    rw [harperConsEmbApply, harperConsEmbApply] at heq
    have hcongr := congrFun heq 0
    simp only [Fin.cons_zero] at hcongr
    simp at hcongr
  conv_lhs => rw [hA]
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]

private theorem harperSliceImageSubset (n : ℕ) (A : Finset (Fin (n + 1) → Bool)) :
    ((Hamming.expansion (harperCubeSlice n A false) 1 ∪ harperCubeSlice n A true).map
      (harperConsEmb n false) ⊆ Hamming.expansion A 1) ∧
    ((Hamming.expansion (harperCubeSlice n A true) 1 ∪ harperCubeSlice n A false).map
      (harperConsEmb n true) ⊆ Hamming.expansion A 1) := by
  constructor
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hz
    rw [harperConsEmbApply]
    rcases Finset.mem_union.mp hy with hyN | hyA
    · obtain ⟨a, ha, hdist⟩ := Hamming.mem_expansion.mp hyN
      exact Hamming.mem_expansion_of_mem ((harperCubeSliceMem n A false a).mp ha)
        (by rwa [harperHammingDistConsEq])
    · exact Hamming.mem_expansion_of_mem ((harperCubeSliceMem n A true y).mp hyA)
        (harperHammingDistConsLe n false true y)
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hz
    rw [harperConsEmbApply]
    rcases Finset.mem_union.mp hy with hyN | hyA
    · obtain ⟨a, ha, hdist⟩ := Hamming.mem_expansion.mp hyN
      exact Hamming.mem_expansion_of_mem ((harperCubeSliceMem n A true a).mp ha)
        (by rwa [harperHammingDistConsEq])
    · exact Hamming.mem_expansion_of_mem ((harperCubeSliceMem n A false y).mp hyA)
        (harperHammingDistConsLe n true false y)

private theorem harperSliceUnionCard (n : ℕ) (A : Finset (Fin (n + 1) → Bool)) :
    (Hamming.expansion (harperCubeSlice n A false) 1 ∪ harperCubeSlice n A true).card
      + (Hamming.expansion (harperCubeSlice n A true) 1
        ∪ harperCubeSlice n A false).card
      ≤ (Hamming.expansion A 1).card := by
  obtain ⟨h0, h1⟩ := harperSliceImageSubset n A
  have hdisj : Disjoint
      ((Hamming.expansion (harperCubeSlice n A false) 1 ∪ harperCubeSlice n A true).map
        (harperConsEmb n false))
      ((Hamming.expansion (harperCubeSlice n A true) 1 ∪ harperCubeSlice n A false).map
        (harperConsEmb n true)) := by
    rw [Finset.disjoint_left]
    intro z hz0 hz1
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hz0
    obtain ⟨y', _, heq⟩ := Finset.mem_map.mp hz1
    rw [harperConsEmbApply, harperConsEmbApply] at heq
    have hcongr := congrFun heq 0
    simp only [Fin.cons_zero] at hcongr
    simp at hcongr
  calc (Hamming.expansion (harperCubeSlice n A false) 1 ∪ harperCubeSlice n A true).card
        + (Hamming.expansion (harperCubeSlice n A true) 1
          ∪ harperCubeSlice n A false).card
      = (((Hamming.expansion (harperCubeSlice n A false) 1
          ∪ harperCubeSlice n A true).map (harperConsEmb n false)) ∪
        ((Hamming.expansion (harperCubeSlice n A true) 1
          ∪ harperCubeSlice n A false).map (harperConsEmb n true))).card := by
        rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]
    _ ≤ (Hamming.expansion A 1).card :=
        Finset.card_le_card (Finset.union_subset h0 h1)

private theorem harperSliceLe0 (n : ℕ) (A : Finset (Fin (n + 1) → Bool)) :
    (Hamming.expansion (harperCubeSlice n A false) 1).card
      + max (harperCubeSlice n A false).card
        (Hamming.expansion (harperCubeSlice n A true) 1).card
      ≤ (Hamming.expansion A 1).card := by
  have h := harperSliceUnionCard n A
  have g0 : (Hamming.expansion (harperCubeSlice n A false) 1).card
      ≤ (Hamming.expansion (harperCubeSlice n A false) 1
        ∪ harperCubeSlice n A true).card :=
    Finset.card_le_card Finset.subset_union_left
  have g1 : max (harperCubeSlice n A false).card
      (Hamming.expansion (harperCubeSlice n A true) 1).card
      ≤ (Hamming.expansion (harperCubeSlice n A true) 1
        ∪ harperCubeSlice n A false).card := by
    apply max_le
    · exact Finset.card_le_card Finset.subset_union_right
    · exact Finset.card_le_card Finset.subset_union_left
  omega

private theorem harperSliceLe1 (n : ℕ) (A : Finset (Fin (n + 1) → Bool)) :
    (Hamming.expansion (harperCubeSlice n A true) 1).card
      + max (harperCubeSlice n A true).card
        (Hamming.expansion (harperCubeSlice n A false) 1).card
      ≤ (Hamming.expansion A 1).card := by
  have h := harperSliceUnionCard n A
  have g0 : (Hamming.expansion (harperCubeSlice n A true) 1).card
      ≤ (Hamming.expansion (harperCubeSlice n A true) 1
        ∪ harperCubeSlice n A false).card :=
    Finset.card_le_card Finset.subset_union_left
  have g1 : max (harperCubeSlice n A true).card
      (Hamming.expansion (harperCubeSlice n A false) 1).card
      ≤ (Hamming.expansion (harperCubeSlice n A false) 1
        ∪ harperCubeSlice n A true).card := by
    apply max_le
    · exact Finset.card_le_card Finset.subset_union_right
    · exact Finset.card_le_card Finset.subset_union_left
  omega

private theorem harperChordLeCardExpansionOne (n : ℕ)
    (A : Finset (Fin n → Bool)) :
    chord n A.card ≤ ((Hamming.expansion A 1).card : ℚ) := by
  induction n with
  | zero =>
    by_cases hA : A = ∅
    · subst hA
      simp [chord_zero]
    · have hne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA
      have h1 : (1 : ℚ) ≤ ((Hamming.expansion A 1).card : ℚ) := by
        have hpos : 0 < (Hamming.expansion A 1).card := by
          calc 0 < A.card := Finset.card_pos.mpr hne
            _ ≤ (Hamming.expansion A 1).card :=
              Finset.card_le_card (Hamming.subset_expansion_self A 1)
        exact_mod_cast hpos
      have h2 : chord 0 A.card ≤ 1 := by
        have hle := chord_le_pow 0 A.card
        simpa using hle
      exact le_trans h2 h1
  | succ n IH =>
    have hcard : A.card = (harperCubeSlice n A false).card
        + (harperCubeSlice n A true).card := harperCardSliceAdd n A
    have hb0 : (harperCubeSlice n A false).card ≤ 2 ^ n :=
      harperCardSliceLe n A false
    have hb1 : (harperCubeSlice n A true).card ≤ 2 ^ n :=
      harperCardSliceLe n A true
    have ih0 : chord n (harperCubeSlice n A false).card
        ≤ (((Hamming.expansion (harperCubeSlice n A false) 1).card : ℕ) : ℚ) :=
      IH _
    have ih1 : chord n (harperCubeSlice n A true).card
        ≤ (((Hamming.expansion (harperCubeSlice n A true) 1).card : ℕ) : ℚ) :=
      IH _
    by_cases hle : (harperCubeSlice n A true).card
        ≤ (harperCubeSlice n A false).card
    · have hN6 := chord_combine (n := n)
        (u := (harperCubeSlice n A false).card)
        (v := (harperCubeSlice n A true).card) hle hb0
      have hN9 := harperSliceLe0 n A
      rw [hcard]
      calc chord (n + 1)
            ((harperCubeSlice n A false).card + (harperCubeSlice n A true).card)
          ≤ chord n (harperCubeSlice n A false).card
            + max ((harperCubeSlice n A false).card : ℚ)
              (chord n (harperCubeSlice n A true).card) := hN6
        _ ≤ (((Hamming.expansion (harperCubeSlice n A false) 1).card : ℕ) : ℚ)
            + max (((harperCubeSlice n A false).card : ℕ) : ℚ)
              (((Hamming.expansion (harperCubeSlice n A true) 1).card : ℕ) : ℚ) :=
            add_le_add ih0 (max_le_max le_rfl ih1)
        _ ≤ (((Hamming.expansion A 1).card : ℕ) : ℚ) := by
            exact_mod_cast hN9
    · push Not at hle
      have hle' : (harperCubeSlice n A false).card
          ≤ (harperCubeSlice n A true).card := le_of_lt hle
      have hcard' : A.card = (harperCubeSlice n A true).card
          + (harperCubeSlice n A false).card := by omega
      have hN6 := chord_combine (n := n)
        (u := (harperCubeSlice n A true).card)
        (v := (harperCubeSlice n A false).card) hle' hb1
      have hN9 := harperSliceLe1 n A
      rw [hcard']
      calc chord (n + 1)
            ((harperCubeSlice n A true).card + (harperCubeSlice n A false).card)
          ≤ chord n (harperCubeSlice n A true).card
            + max ((harperCubeSlice n A true).card : ℚ)
              (chord n (harperCubeSlice n A false).card) := hN6
        _ ≤ (((Hamming.expansion (harperCubeSlice n A true) 1).card : ℕ) : ℚ)
            + max (((harperCubeSlice n A true).card : ℕ) : ℚ)
              (((Hamming.expansion (harperCubeSlice n A false) 1).card : ℕ) : ℚ) :=
            add_le_add ih1 (max_le_max le_rfl ih0)
        _ ≤ (((Hamming.expansion A 1).card : ℕ) : ℚ) := by
            exact_mod_cast hN9

private theorem harperExpansionAddOne {ι F : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype F] [DecidableEq F] (A : Finset (ι → F)) (t : ℕ) :
    Hamming.expansion (Hamming.expansion A t) 1
      ⊆ Hamming.expansion A (t + 1) := by
  intro x hx
  rw [Hamming.mem_expansion] at hx
  obtain ⟨b, hb, hxb⟩ := hx
  obtain ⟨a, ha, hab⟩ := Hamming.mem_expansion.mp hb
  refine Hamming.mem_expansion.mpr ⟨a, ha, ?_⟩
  calc hammingDist x a ≤ hammingDist x b + hammingDist b a :=
        hammingDist_triangle _ _ _
    _ ≤ 1 + t := Nat.add_le_add hxb hab
    _ = t + 1 := by omega

private theorem harperBallVolLeCardExpansion (n : ℕ)
    (A : Finset (Fin n → Bool)) (e : ℕ) (hle : ballVol n e ≤ A.card) (t : ℕ) :
    ballVol n (e + t) ≤ (Hamming.expansion A t).card := by
  induction t with
  | zero =>
    calc ballVol n (e + 0) = ballVol n e := by simp
      _ ≤ A.card := hle
      _ ≤ (Hamming.expansion A 0).card :=
        Finset.card_le_card (Hamming.subset_expansion_self A 0)
  | succ t IH =>
    have hrw : e + (t + 1) = (e + t) + 1 := by omega
    rw [hrw]
    have h1 : ((ballVol n ((e + t) + 1) : ℕ) : ℚ)
        = chord n (ballVol n (e + t)) := (harperChordBallVolAll n (e + t)).symm
    have h2 : chord n (ballVol n (e + t))
        ≤ chord n ((Hamming.expansion A t).card) := chord_mono IH
    have h3 : chord n ((Hamming.expansion A t).card)
        ≤ ((((Hamming.expansion (Hamming.expansion A t) 1).card : ℕ)) : ℚ) :=
      harperChordLeCardExpansionOne n _
    have h4 : (Hamming.expansion (Hamming.expansion A t) 1).card
        ≤ (Hamming.expansion A (t + 1)).card :=
      Finset.card_le_card (harperExpansionAddOne _ t)
    have h5 : ((ballVol n ((e + t) + 1) : ℕ) : ℚ)
        ≤ ((((Hamming.expansion A (t + 1)).card : ℕ)) : ℚ) := by
      calc ((ballVol n ((e + t) + 1) : ℕ) : ℚ)
            = chord n (ballVol n (e + t)) := h1
        _ ≤ chord n ((Hamming.expansion A t).card) := h2
        _ ≤ ((((Hamming.expansion (Hamming.expansion A t) 1).card : ℕ)) : ℚ) := h3
        _ ≤ ((((Hamming.expansion A (t + 1)).card : ℕ)) : ℚ) := by
            exact_mod_cast h4
    exact_mod_cast h5

/--
**Harper's isoperimetric inequality on the Hamming cube.** Let $n$ be a natural number. For
points $x, y \in \{0,1\}^n$, write $d_H(x, y)$ for the Hamming distance between them, the number
of coordinates in which they differ. For a set $S \subseteq \{0,1\}^n$ and a natural number $t$,
write $S_t$ for the set of points $x \in \{0,1\}^n$ with $d_H(x, s) \le t$ for some $s \in S$.
Let $A$ and $B$ be subsets of $\{0,1\}^n$ such that $B$ is a closed Hamming ball, that is,
$B = \{x : d_H(c, x) \le e\}$ for some $c \in \{0,1\}^n$ and some natural number $e$, and such
that $|B| \le |A|$. Then $|B_t| \le |A_t|$ for every natural number $t \ge 1$.

This is only the ball-comparison form of Harper's theorem: it does not assert that a ball
exists at every cardinality and gives no equality cases.

Source: ATLAS ProbabilisticMethodsInCombinatorics, Theorem 9.4.3 (definitions and theorem at
lines 17--51 of `code/Chapter9/HarperIsoperimetric.lean`, target metadata at lines 749--753
of `targets.yaml`, report entry at lines 3800--3826 of `report.json`, all under
`v1/Atlas/ProbabilisticMethodsInCombinatorics` at commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`); the course text cites Harper without proof.

Source: L. H. Harper, "Optimal numberings and isoperimetric problems on graphs,"
Journal of Combinatorial Theory 1(3) (1966), 385–393, DOI 10.1016/S0021-9800(66)80059-5.

Proves `Wanted` entry `harper_isoperimetric_inequality`.
-/
theorem harper_isoperimetric_inequality
    {n : ℕ}
    (A B : Finset (Fin n → Bool))
    (hB : Hamming.IsBall B)
    (hcard : B.card ≤ A.card)
    (t : ℕ)
    (ht : 0 < t) :
    (Hamming.expansion B t).card ≤ (Hamming.expansion A t).card := by
  obtain ⟨c, e, rfl⟩ := hB
  obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt ht)
  have hle : ballVol n e ≤ A.card := by
    have hBe : (Hamming.ball c e).card = ballVol n e := ballVol_card_ball c e
    omega
  have hstep : ballVol n (e + (t' + 1)) ≤ (Hamming.expansion A (t' + 1)).card :=
    harperBallVolLeCardExpansion n A e hle (t' + 1)
  have hball : (Hamming.ball c (e + (t' + 1))).card = ballVol n (e + (t' + 1)) :=
    ballVol_card_ball c (e + (t' + 1))
  rw [expansion_ball_eq c e (t' + 1), hball]
  exact hstep

end MathlibExt.Combinatorics.HarperIsoperimetricWanted
end
