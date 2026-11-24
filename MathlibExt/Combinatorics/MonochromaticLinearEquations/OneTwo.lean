/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.MonochromaticLinearEquations.Recolouring
import all MathlibExt.Combinatorics.MonochromaticLinearEquations.Recolouring
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Uncommonness of the equation x + 2y = z + 2w

We prove `MetaMathlibExt.isUncommonOverIntegers_one_two_neg_one_neg_two` using a
two-colour construction and recolouring. Following the step-function approach of
Dong, Mani, Pham and Tidor, we bias independent colours on equal subintervals.
A discrete count on 26 blocks checks the deficit separately for every possible carry
in the equation on block indices.
-/

namespace MetaMathlibExt
namespace isUncommonOverIntegers_one_two_neg_one_neg_two

open Finset Filter isUncommonOverIntegers_of_two

private abbrev coeff : Fin 4 → ℤ := ![1, 2, -1, -2]

private lemma equation (v : Fin 4 → ℤ) :
    ∑ i, coeff i * v i = 0 ↔ v 0 + 2 * v 1 - 2 * v 3 = v 2 := by
  simp [coeff, Fin.sum_univ_succ]
  omega

-- The numbers of red labels (out of 128) on the successive blocks.
private def threshold (i : ℤ) : Fin 128 :=
  [64, 65, 63, 60, 66, 67, 64, 67, 65, 61, 61, 66, 63,
   63, 66, 61, 61, 65, 67, 64, 67, 66, 60, 63, 65, 64][i.toNat]?.getD 64

private def red (i : ℤ) : ℕ := threshold i

private def blue (i : ℤ) : ℕ := 128 - red i

private abbrev Triple := ℤ × ℤ × ℤ

private def box (n : ℕ) : Finset Triple :=
  Ico (0 : ℤ) n ×ˢ Ico (0 : ℤ) n ×ˢ Ico (0 : ℤ) n

private def linear (p : Triple) : ℤ := p.1 + 2 * p.2.1 - 2 * p.2.2

private def indices (d : ℤ) : Finset Triple :=
  (box 26).filter fun p => linear p + d ∈ Ico (0 : ℤ) 26

private def weight (f : ℤ → ℕ) (d : ℤ) (p : Triple) : ℕ :=
  f p.1 * f p.2.1 * f (linear p + d) * f p.2.2

private def mass (f : ℤ → ℕ) (d : ℤ) := ∑ p ∈ indices d, weight f d p

-- Group the two sides of the equation by their common weighted sum, up to the carry.
private def pairTerm (f : ℤ → ℕ) (t y : ℤ) : ℕ :=
  if 0 ≤ t - 2 * y ∧ t - 2 * y < 26 then f (t - 2 * y) * f y else 0

private def pairMass (f : ℤ → ℕ) (t : ℤ) : ℕ :=
  ∑ y ∈ Ico (0 : ℤ) 26, pairTerm f t y

private def correlation (f : ℤ → ℕ) (d : ℤ) : ℕ :=
  ∑ t ∈ Ico (0 : ℤ) 76, pairMass f t * pairMass f (t + d)

set_option maxRecDepth 2048 in
private lemma mass_eq (f : ℤ → ℕ) (d : ℤ) : mass f d = correlation f d := by
  let grid := Ico (0 : ℤ) 76 ×ˢ Ico (0 : ℤ) 26 ×ˢ Ico (0 : ℤ) 26
  let valid (p : Triple) := (0 ≤ p.1 - 2 * p.2.1 ∧ p.1 - 2 * p.2.1 < 26) ∧
    (0 ≤ p.1 + d - 2 * p.2.2 ∧ p.1 + d - 2 * p.2.2 < 26)
  let term (p : Triple) := pairTerm f p.1 p.2.1 * pairTerm f (p.1 + d) p.2.2
  have reindex : mass f d = ∑ p ∈ grid.filter valid, term p := by
    apply sum_nbij' (fun p => (p.1 + 2 * p.2.1, p.2)) (fun p => (p.1 - 2 * p.2.1, p.2))
    · rintro ⟨x, y, w⟩ hp
      simp [indices, box, linear] at hp
      simp [grid, valid]
      omega
    · rintro ⟨t, y, w⟩ hp
      simp [grid, valid] at hp
      simp [indices, box, linear]
      omega
    · rintro ⟨x, y, w⟩ _
      simp
    · rintro ⟨t, y, w⟩ _
      simp
    · rintro ⟨x, y, w⟩ hp
      simp only [indices, mem_filter, box, mem_product, mem_Ico, Nat.cast_ofNat, linear] at hp
      dsimp [term, weight, linear, pairTerm]
      rw [show x + 2 * y - 2 * y = x by ring,
        show x + 2 * y + d - 2 * w = x + 2 * y - 2 * w + d by ring]
      simp [hp, mul_assoc]
  have drop : ∀ p ∈ grid, (if valid p then term p else 0) = term p := by
    rintro ⟨t, y, w⟩ _
    by_cases hx : 0 ≤ t - 2 * y ∧ t - 2 * y < 26
    · by_cases hz : 0 ≤ t + d - 2 * w ∧ t + d - 2 * w < 26 <;>
        simp only [valid, term, pairTerm, hx, hz, and_self, and_false, ↓reduceIte, mul_zero]
    · simp only [valid, term, pairTerm, hx, false_and, ↓reduceIte, zero_mul]
  rw [reindex, sum_filter, sum_congr rfl drop]
  simp only [correlation, pairMass, grid, sum_product, term, sum_mul, mul_sum]
  exact sum_congr rfl fun _ _ => sum_comm

private lemma count_eq (d : ℤ) : (indices d).card = correlation (fun _ => 1) d := by
  rw [← mass_eq]
  simp [mass, weight]

-- Fix all four remainders modulo the block length. The block index of z is then
-- determined by the other three block indices and the carry d.
private lemma certificate (d : ℤ) (hl : -2 ≤ d) (hu : d ≤ 2) :
    8 * (mass red d + mass blue d) + (indices d).card ≤ 128 ^ 4 * (indices d).card := by
  rw [mass_eq, mass_eq, count_eq]
  interval_cases d <;> decide +kernel

private abbrev Quad := Fin 4 → ℤ

private def block (m : ℕ) (z : ℤ) : ℤ := (z - 1) / m

private def remainder (m : ℕ) (v : Quad) : Quad := fun i => (v i - 1) % m

private def form (v : Quad) : ℤ := v 0 + 2 * v 1 - v 2 - 2 * v 3

private def coarse (d : ℤ) (p : Triple) : Quad := ![p.1, p.2.1, linear p + d, p.2.2]

private def project (v : Quad) : Triple := (v 0, v 1, v 3)

private def bounds (n : ℕ) (v : Quad) := ∀ i, 0 ≤ v i ∧ v i < n

private lemma mem_indices {d : ℤ} {p : Triple} : p ∈ indices d ↔ bounds 26 (coarse d p) := by
  simp [indices, box, bounds, coarse, Fin.forall_fin_succ, and_assoc, and_left_comm, and_comm]

private lemma form_coarse (d : ℤ) (p : Triple) : form (coarse d p) = -d := by
  simp [form, coarse, linear]
  ring

private lemma coarse_project {d : ℤ} {v : Quad} (h : form v = -d) :
    coarse d (project v) = v := by
  funext i
  simp only [form] at h
  fin_cases i <;> simp [coarse, project, linear]
  omega

private lemma mem_sol {v : Quad} {n : ℕ} :
    v ∈ solutions coeff n ↔ (∀ i, 1 ≤ v i ∧ v i ≤ n) ∧ form v = 0 := by
  rw [mem_solutions, equation]
  apply and_congr_right
  intro _
  unfold form
  omega

private lemma digits_spec {m : ℕ} (hm : 0 < m) (v : Quad) :
    bounds m (remainder m v) ∧ ∀ i, v i = 1 + remainder m v i + m * block m (v i) := by
  have hpos : (0 : ℤ) < m := by exact_mod_cast hm
  refine ⟨fun i => ⟨Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩, fun i => ?_⟩
  unfold block remainder
  rw [add_assoc, Int.emod_add_mul_ediv]
  omega

private def joinDigits (m : ℕ) (q b : Quad) : Quad := fun i => 1 + q i + m * b i

private lemma form_join (m : ℕ) (q b : Quad) :
    form (joinDigits m q b) = form q + m * form b := by
  simp [form, joinDigits]
  ring

private lemma split_join {m : ℕ} (hm : 0 < m) {q : Quad} (hq : bounds m q) (b : Quad) :
    remainder m (joinDigits m q b) = q ∧ block m ∘ joinDigits m q b = b := by
  have hpos : (0 : ℤ) < m := by exact_mod_cast hm
  constructor <;> funext i
  · simpa [remainder, joinDigits, add_assoc, Int.add_mul_emod_self_left] using
      Int.emod_eq_of_lt (hq i).1 (hq i).2
  · simp [block, joinDigits, add_assoc, Int.add_mul_ediv_left _ _ hpos.ne',
      Int.ediv_eq_zero_of_lt (hq i).1 (hq i).2]

private lemma blocks_bounded {m : ℕ} (hm : 0 < m) {v : Quad}
    (hv : v ∈ solutions coeff (26 * m)) : bounds 26 (block m ∘ v) := by
  have hpos : (0 : ℤ) < m := by exact_mod_cast hm
  intro i
  obtain ⟨hl, hu⟩ := (mem_sol.mp hv).1 i
  change 0 ≤ (v i - 1) / m ∧ (v i - 1) / m < 26
  rw [Int.ediv_lt_iff_lt_mul hpos]
  push_cast at hu
  exact ⟨Int.ediv_nonneg (by omega) hpos.le, by omega⟩

private def tupleWeight (f : ℤ → ℕ) (v : Quad) : ℕ := ∏ i, f (v i)

-- All solutions with remainder vector q are in bijection with the block triples at carry d.
private lemma fibre_sum {m : ℕ} (hm : 0 < m) {q : Quad} (hq : bounds m q)
    {d : ℤ} (hd : form q = m * d) (f : ℤ → ℕ) :
    ∑ v ∈ (solutions coeff (26 * m)).filter (fun v => remainder m v = q),
        tupleWeight f (block m ∘ v) = mass f d := by
  have hpos : (0 : ℤ) < m := by exact_mod_cast hm
  let lift (p : Triple) := joinDigits m q (coarse d p)
  have split (v : Quad) (hs : v ∈ solutions coeff (26 * m)) (hr : remainder m v = q) :
      form (block m ∘ v) = -d := by
    have hv : v = joinDigits m q (block m ∘ v) := by
      rw [← hr]
      exact funext (digits_spec hm v).2
    have he := (mem_sol.mp hs).2
    rw [hv, form_join, hd, ← mul_add] at he
    rcases mul_eq_zero.mp he with h | h <;> omega
  apply sum_nbij' (fun v => project (block m ∘ v)) lift
  · intro v hv
    obtain ⟨hs, hr⟩ := mem_filter.mp hv
    rw [mem_indices, coarse_project (split v hs hr)]
    exact blocks_bounded hm hs
  · intro p hp
    have hb := mem_indices.mp hp
    refine mem_filter.mpr ⟨mem_sol.mpr ⟨fun i => ?_, ?_⟩, (split_join hm hq _).1⟩
    · have := hq i
      have hi := hb i
      change 1 ≤ 1 + q i + (m : ℤ) * coarse d p i ∧
        1 + q i + (m : ℤ) * coarse d p i ≤ ↑(26 * m)
      push_cast
      constructor
      · nlinarith [mul_nonneg hpos.le hi.1]
      · have hle : coarse d p i ≤ 25 := by omega
        nlinarith [mul_le_mul_of_nonneg_left hle hpos.le]
    · change form (joinDigits m q (coarse d p)) = 0
      rw [form_join, form_coarse, hd]
      ring
  · intro v hv
    obtain ⟨hs, hr⟩ := mem_filter.mp hv
    dsimp only [lift]
    rw [coarse_project (split v hs hr), ← hr]
    exact (funext (digits_spec hm v).2).symm
  · intro p _
    change project (block m ∘ joinDigits m q (coarse d p)) = p
    rw [(split_join hm hq _).2]
    rfl
  · intro v hv
    obtain ⟨hs, hr⟩ := mem_filter.mp hv
    have he := congrFun (coarse_project (split v hs hr)) 2
    change linear (project (block m ∘ v)) + d = block m (v 2) at he
    rw [weight, he]
    simp [project, tupleWeight, Fin.prod_univ_succ, mul_assoc]

private lemma weighted_bound {m : ℕ} (hm : 0 < m) :
    let s := solutions coeff (26 * m)
    8 * (∑ v ∈ s, (tupleWeight red (block m ∘ v) + tupleWeight blue (block m ∘ v))) +
      s.card ≤ 128 ^ 4 * s.card := by
  classical
  let s := solutions coeff (26 * m)
  let digits := Fintype.piFinset fun _ : Fin 4 => Ico (0 : ℤ) m
  let fibre (q : Quad) := s.filter fun v => remainder m v = q
  let val (v : Quad) := tupleWeight red (block m ∘ v) + tupleWeight blue (block m ∘ v)
  have maps (v) (_ : v ∈ s) : remainder m v ∈ digits :=
    Fintype.mem_piFinset.mpr fun i => mem_Ico.mpr ((digits_spec hm v).1 i)
  have sum_fibres (f : Quad → ℕ) : ∑ q ∈ digits, ∑ v ∈ fibre q, f v = ∑ v ∈ s, f v :=
    sum_fiberwise_of_maps_to maps f
  have cards : ∑ q ∈ digits, (fibre q).card = s.card := by simpa using sum_fibres (fun _ => 1)
  change 8 * (∑ v ∈ s, val v) + s.card ≤ 128 ^ 4 * s.card
  rw [← sum_fibres, ← cards, mul_sum, ← sum_add_distrib, mul_sum]
  apply sum_le_sum
  intro q hq
  by_cases hn : (fibre q).Nonempty
  · obtain ⟨v, hv⟩ := hn
    obtain ⟨hs, hr⟩ := mem_filter.mp hv
    have hb : bounds m q := fun i => mem_Ico.mp (Fintype.mem_piFinset.mp hq i)
    let d := -form (block m ∘ v)
    have hd : form q = m * d := by
      have hj : v = joinDigits m q (block m ∘ v) := by
        rw [← hr]
        exact funext (digits_spec hm v).2
      have he := (mem_sol.mp hs).2
      rw [hj, form_join] at he
      dsimp [d]
      linarith
    have hlo : -2 ≤ d := by
      by_contra! h
      have := mul_le_mul_of_nonneg_left (show d ≤ -3 by omega) (Int.natCast_nonneg m)
      dsimp [form] at hd
      linarith [(hb 0).1, (hb 1).1, (hb 2).2, (hb 3).2]
    have hhi : d ≤ 2 := by
      by_contra! h
      have := mul_le_mul_of_nonneg_left (show 3 ≤ d by omega) (Int.natCast_nonneg m)
      dsimp [form] at hd
      linarith [(hb 0).2, (hb 1).2, (hb 2).1, (hb 3).1]
    have hc : (fibre q).card = (indices d).card := by
      simpa [tupleWeight, mass, weight, fibre, s] using fibre_sum hm hb hd (fun _ => 1)
    dsimp only [val]
    rw [sum_add_distrib, hc, fibre_sum hm hb hd red, fibre_sum hm hb hd blue]
    exact certificate d hlo hhi
  · simp [not_nonempty_iff_eq_empty.mp hn]

-- Among independent labels, the restrictions at four distinct vertices multiply.
private lemma label_count {V : Type*} [Fintype V] [DecidableEq V] (y : Fin 4 → V)
    (hy : Function.Injective y) (A : V → Finset (Fin 128)) :
    128 ^ 4 * (univ.filter (fun w : V → Fin 128 => ∀ i, w (y i) ∈ A (y i))).card =
      Fintype.card (V → Fin 128) * ∏ i, (A (y i)).card := by
  classical
  let t := univ.image y
  have ht : t.card = 4 := by simp [t, card_image_of_injective _ hy]
  let choices (v : V) := if v ∈ t then A v else univ
  have hc : univ.filter (fun w : V → Fin 128 => ∀ i, w (y i) ∈ A (y i)) =
      Fintype.piFinset choices := by
    ext w
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h v
      by_cases hv : v ∈ t
      · obtain ⟨i, _, rfl⟩ := mem_image.mp hv
        simpa [choices, hv] using h i
      · simp [choices, hv]
    · intro h i
      simpa [choices, t] using h (y i)
  rw [hc, Fintype.card_piFinset, ← prod_sdiff (s₁ := t) (s₂ := univ) (by simp)]
  have hout : (∏ v ∈ univ \ t, (choices v).card) = 128 ^ (Fintype.card V - 4) := by
    calc
      _ = ∏ _v ∈ univ \ t, 128 :=
        prod_congr rfl fun v hv => by simp [choices, (mem_sdiff.mp hv).2]
      _ = _ := by simp [card_sdiff_of_subset, ht]
  have hin : (∏ v ∈ t, (choices v).card) = ∏ i, (A (y i)).card := by
    rw [show t = univ.image y from rfl, prod_image hy.injOn]
    simp [choices, t]
  have hk : 4 ≤ Fintype.card V := by simpa using Fintype.card_le_of_injective y hy
  rw [hout, hin, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hk]
  simp

-- Average the number of monochromatic solutions over all assignments of labels.
private lemma round_colours (m : ℕ) :
    let s := solutions coeff (26 * m)
    ∃ χ : ℤ → Fin 2, 128 ^ 4 * (s.filter (mono χ)).card ≤
      (∑ v ∈ s, (tupleWeight red (block m ∘ v) + tupleWeight blue (block m ∘ v))) +
        128 ^ 4 * (repeats s).card := by
  classical
  let n := 26 * m
  let s := solutions coeff n
  let V := ↥(Icc (1 : ℤ) n)
  let W := V → Fin 128
  let A (v : V) := Iio (threshold (block m v))
  let colour (w : W) (z : ℤ) : Fin 2 :=
    if h : z ∈ Icc (1 : ℤ) n then if w ⟨z, h⟩ ∈ A ⟨z, h⟩ then 0 else 1 else 1
  let val (v : Quad) := tupleWeight red (block m ∘ v) + tupleWeight blue (block m ∘ v)
  let bound (v : Quad) := val v + if Function.Injective v then 0 else 128 ^ 4
  have point (v : Quad) (hv : v ∈ s) :
      128 ^ 4 * (univ.filter fun w : W => mono (colour w) v).card ≤ Fintype.card W * bound v := by
    by_cases hi : Function.Injective v
    · have hx (i) : v i ∈ Icc (1 : ℤ) n := mem_Icc.mpr ((mem_sol.mp hv).1 i)
      let y (i : Fin 4) : V := ⟨v i, hx i⟩
      have hy : Function.Injective y := fun _ _ h => hi (congrArg Subtype.val h)
      let allIn (B : V → Finset (Fin 128)) := univ.filter fun w : W => ∀ i, w (y i) ∈ B (y i)
      have cover : (univ.filter fun w : W => mono (colour w) v) ⊆
          allIn A ∪ allIn (fun u => (A u)ᶜ) := by
        intro w hw
        have mono' (i) := (mem_filter.mp hw).2 i 0
        simp only [colour, dite_eq_left (hx _)] at mono'
        by_cases h : w (y 0) ∈ A (y 0)
        · apply mem_union_left
          exact mem_filter.mpr ⟨mem_univ _, fun i => by simpa [y, h] using mono' i⟩
        · apply mem_union_right
          exact mem_filter.mpr ⟨mem_univ _, fun i => by simpa [y, h] using mono' i⟩
      have hle := Nat.mul_le_mul_left (128 ^ 4) ((card_le_card cover).trans (card_union_le _ _))
      rw [Nat.mul_add, label_count y hy A, label_count y hy (fun u => (A u)ᶜ)] at hle
      simpa [bound, hi, val, tupleWeight, A, y, W, blue, red, card_compl, Nat.mul_add] using hle
    · have h := Nat.mul_le_mul_left (128 ^ 4)
        (card_le_univ (univ.filter fun w : W => mono (colour w) v))
      calc
        _ ≤ 128 ^ 4 * Fintype.card W := h
        _ ≤ _ := by rw [mul_comm]; apply Nat.mul_le_mul_left; simp [bound, hi]
  have hsum := sum_le_sum point
  have swap : ∑ v ∈ s, (univ.filter fun w : W => mono (colour w) v).card =
      ∑ w : W, (s.filter (mono (colour w))).card := by
    simp_rw [card_filter]
    rw [sum_comm]
  have hb : ∑ v ∈ s, bound v = (∑ v ∈ s, val v) + 128 ^ 4 * (repeats s).card := by
    simp [bound, sum_add_distrib, sum_ite, repeats, mul_comm]
  rw [← mul_sum, swap, ← mul_sum, hb] at hsum
  change ∃ χ, 128 ^ 4 * (s.filter (mono χ)).card ≤
    (∑ v ∈ s, val v) + 128 ^ 4 * (repeats s).card
  by_contra! h
  have strict := sum_lt_sum_of_nonempty (univ_nonempty (α := W)) fun w _ => h (colour w)
  simp only [sum_const, card_univ, smul_eq_mul, ← mul_sum] at strict
  exact (not_lt_of_ge hsum) strict

private lemma nonzero (i : Fin 4) : coeff i ≠ 0 := by fin_cases i <;> decide

-- The errors from repeated coordinates use at most a quarter of the certified gap.
private lemma strict_deficit {K M S T D : ℕ} (hK : 0 < K) (hS : 0 < S)
    (hrep : 32 * K * D ≤ S) (hw : 8 * T + S ≤ K * S) (hχ : K * M ≤ T + K * D) :
    8 * (M : ℝ) < (1 - 1 / (2 * (K : ℝ))) * S := by
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hs : 0 < (S : ℝ) := by exact_mod_cast hS
  have hr : 32 * (K : ℝ) * D ≤ S := by exact_mod_cast hrep
  have ht : 8 * (T : ℝ) + S ≤ (K : ℝ) * S := by exact_mod_cast hw
  have hm : (K : ℝ) * M ≤ T + (K : ℝ) * D := by exact_mod_cast hχ
  field_simp
  linarith only [hs, hr, ht, hm]

private lemma two_colours : IsUncommonOverIntegers coeff 2 := by
  let K : ℕ := 128 ^ 4
  have hk : 0 < K := by decide
  have sparse := sparse_repeats (by decide : 3 ≤ 4) coeff (fun _ => 1) nonzero
    (fun _ => by decide) ((equation _).mpr (by norm_num)) (32 * K)
  obtain ⟨N, hN⟩ := eventually_atTop.mp sparse
  apply (uncommon_iff coeff).mpr
  refine ⟨1 / (2 * (K : ℝ)), by positivity, frequently_atTop.mpr fun n => ?_⟩
  let m := max n N + 1
  have hm : 0 < m := Nat.succ_pos _
  have hnm : n ≤ 26 * m := by dsimp [m]; omega
  have hNm : N ≤ 26 * m := by dsimp [m]; omega
  let s := solutions coeff (26 * m)
  let total := ∑ v ∈ s, (tupleWeight red (block m ∘ v) + tupleWeight blue (block m ∘ v))
  obtain ⟨χ, hχ⟩ := round_colours m
  refine ⟨26 * m, hnm, χ, ?_⟩
  have hrep : 32 * K * (repeats s).card ≤ s.card := hN _ hNm
  have hw : 8 * total + s.card ≤ K * s.card := weighted_bound hm
  have hχ' : K * (s.filter (mono χ)).card ≤ total + K * (repeats s).card := hχ
  have hpos : 0 < s.card := card_pos.mpr ⟨fun _ => 1, mem_sol.mpr ⟨fun _ =>
    ⟨by decide, by exact_mod_cast (show 1 ≤ 26 * m by omega)⟩, by norm_num [form]⟩⟩
  rw [show ((2 : ℕ) : ℝ) ^ (4 - 1 : ℕ) = 8 by norm_num]
  exact strict_deficit hk hpos hrep hw hχ'

end isUncommonOverIntegers_one_two_neg_one_neg_two

open isUncommonOverIntegers_one_two_neg_one_neg_two in
/-- **Uncommonness of $x + 2y - z - 2w = 0$ over the integers.** For every $r \ge 2$,
the equation $x + 2y - z - 2w = 0$ is $r$-uncommon over the integers.

Source: Laurence P. Wijaya, *On Monochromatic Solutions of Linear Equations Using at Least
Three Colors*, INTEGERS 25 (2025), Article A88, Corollary 2 (`integers-2025-A88-cor-2`). -/
public theorem isUncommonOverIntegers_one_two_neg_one_neg_two (r : ℕ) (hr : 2 ≤ r) :
    IsUncommonOverIntegers (![1, 2, -1, -2] : Fin 4 → ℤ) r := by
  rcases eq_or_lt_of_le hr with h | h
  · subst r
    exact two_colours
  · exact isUncommonOverIntegers_of_two 4 (by decide) _ nonzero two_colours r (by omega)

end MetaMathlibExt
