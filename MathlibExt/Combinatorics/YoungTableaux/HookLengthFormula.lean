/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.YoungTableaux.HookLength
public import Mathlib.Data.Nat.Factorial.Basic
import all MathlibExt.Combinatorics.YoungTableaux.SumSYTCountSq
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# The hook length formula

The hook length formula was proved by J. S. Frame, G. de B. Robinson and R. M. Thrall in
*The hook graphs of the symmetric group*, Canad. J. Math. 6 (1954), 316–324. It is Theorem 8.1
of Stanley, *Topics in Algebraic Combinatorics*, author's draft of 1 February 2013
(https://math.mit.edu/~rstan/algcomb/algcomb.pdf).

The proof follows C. Greene, A. Nijenhuis and H. S. Wilf, *A probabilistic proof of a formula
for the number of Young tableaux of a given shape*, Adv. Math. 31 (1979), 104–109.

For each Young diagram the tableau count times the product of the hook lengths is the factorial
of the number of cells. From each cell the hook walk jumps uniformly to a cell strictly to its
right or strictly below it, stopping at a corner. For a fixed corner its endpoint probability
factors into a row weight and a column weight. Summing over starting cells gives the ratio of
hook products before and after deleting that corner. The formula then follows by removing the
largest entry of a tableau.
-/

@[expose] public section

open MathlibExt.Combinatorics.YoungTableaux.HookLength

namespace MathlibExt.Combinatorics.YoungTableaux.HookLengthWanted

open Finset

private abbrev Corner (μ : YoungDiagram) (c : ℕ × ℕ) :=
  μ.rowLen c.1 = c.2 + 1 ∧ μ.colLen c.2 = c.1 + 1

private def corners (μ : YoungDiagram) := μ.cells.filter (Corner μ)

private theorem corner_mem {μ : YoungDiagram} {r s : ℕ} (h : Corner μ (r, s)) :
    (r, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by rw [h.1]; omega)

private theorem corner_bounds {μ : YoungDiagram} {r s i j : ℕ} (h : Corner μ (r, s))
    (hi : i ≤ r) (hj : j ≤ s) : j < μ.rowLen i ∧ i < μ.colLen j := by
  have hm := μ.up_left_mem hi hj (corner_mem h)
  exact ⟨YoungDiagram.mem_iff_lt_rowLen.mp hm, YoungDiagram.mem_iff_lt_colLen.mp hm⟩

/-- In one coordinate of a hook walk ending at `r`, the total weight from indices
`i, …, r` is the product of the factors `1 + 1 / x k`. -/
private def tailWeight (x : ℕ → ℚ) (r i : ℕ) : ℚ :=
  ∏ k ∈ Ico i r, (1 + (x k)⁻¹)

private def pointWeight (x : ℕ → ℚ) (r i : ℕ) : ℚ :=
  if i < r then (x i)⁻¹ * tailWeight x r (i + 1) else if i = r then 1 else 0

private theorem pointWeight_self (x : ℕ → ℚ) (r : ℕ) : pointWeight x r r = 1 := by
  simp [pointWeight]

private theorem pointWeight_after (x : ℕ → ℚ) {r i : ℕ} (hi : r < i) :
    pointWeight x r i = 0 := by simp [pointWeight, hi.not_gt, hi.ne']

private theorem sum_pointWeight (x : ℕ → ℚ) {i r b : ℕ} (hi : i ≤ r) (hb : r < b) :
    ∑ k ∈ Ico i b, pointWeight x r k = tailWeight x r i := by
  induction hi using Nat.decreasingInduction with
  | self =>
    rw [Finset.sum_eq_single r]
    · simp [pointWeight_self, tailWeight]
    · intro k hk hkr
      exact pointWeight_after x (lt_of_le_of_ne (mem_Ico.mp hk).1 hkr.symm)
    · simp [hb]
  | of_succ i hi ih =>
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : i < b), ih]
    simp only [tailWeight, Finset.prod_eq_prod_Ico_succ_bot (by omega : i < r),
      pointWeight, ite_eq_left hi]
    ring

private theorem pointWeight_step (x : ℕ → ℚ) {i r b : ℕ} (hi : i ≤ r) (hb : r < b)
    (hx : x r = 0) (hn : ∀ k < r, x k ≠ 0) :
    x i * pointWeight x r i = ∑ k ∈ Ico (i + 1) b, pointWeight x r k := by
  rcases hi.eq_or_lt with rfl | h
  · rw [hx, zero_mul]
    exact (sum_eq_zero fun k hk => pointWeight_after x (mem_Ico.mp hk).1).symm
  · rw [sum_pointWeight x h hb]
    simp [pointWeight, h, hn i h]

private def excess (μ : YoungDiagram) (i j : ℕ) : ℚ := (hookLength μ (i, j) : ℚ) - 1

private def endpoint (μ : YoungDiagram) (c : ℕ × ℕ) (i j : ℕ) : ℚ :=
  pointWeight (fun k => excess μ k c.2) c.1 i *
    pointWeight (excess μ c.1) c.2 j

private theorem excess_eq {μ : YoungDiagram} {i j : ℕ} (hc : (i, j) ∈ μ) :
    excess μ i j = ((μ.rowLen i - (j + 1) : ℕ) : ℚ) +
      ((μ.colLen j - (i + 1) : ℕ) : ℚ) := by
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp hc
  have hv := YoungDiagram.mem_iff_lt_colLen.mp hc
  have he : hookLength μ (i, j) = (μ.rowLen i - (j + 1)) + (μ.colLen j - (i + 1)) + 1 := by
    unfold hookLength
    dsimp only
    omega
  simp [excess, he]

private theorem excess_corner {μ : YoungDiagram} {r s : ℕ} (hc : Corner μ (r, s)) :
    excess μ r s = 0 := by simp [excess_eq (corner_mem hc), hc.1, hc.2]

private theorem excess_row_ne {μ : YoungDiagram} {r s k : ℕ} (hc : Corner μ (r, s))
    (hk : k < r) : excess μ k s ≠ 0 := by
  rw [excess_eq (μ.up_left_mem hk.le le_rfl (corner_mem hc)), hc.2]
  have h : 0 < r + 1 - (k + 1) := by omega
  positivity

private theorem excess_col_ne {μ : YoungDiagram} {r s k : ℕ} (hc : Corner μ (r, s))
    (hk : k < s) : excess μ r k ≠ 0 := by
  rw [excess_eq (μ.up_left_mem le_rfl hk.le (corner_mem hc)), hc.1]
  have h : 0 < s + 1 - (k + 1) := by omega
  positivity

private theorem endpoint_step {μ : YoungDiagram} {r s : ℕ} (hc : Corner μ (r, s)) (i j : ℕ) :
    excess μ i j * endpoint μ (r, s) i j =
      (∑ k ∈ Ico (i + 1) (μ.colLen j), endpoint μ (r, s) k j) +
      ∑ k ∈ Ico (j + 1) (μ.rowLen i), endpoint μ (r, s) i k := by
  unfold endpoint
  dsimp only [Prod.fst, Prod.snd]
  rw [← sum_mul, ← mul_sum]
  by_cases hi : i ≤ r
  · by_cases hj : j ≤ s
    · have hb := corner_bounds hc hi (le_refl s)
      have hb' := corner_bounds hc (le_refl r) hj
      -- The number of available jumps splits as a sum of the two axial excesses.
      have hs : excess μ i j = excess μ i s + excess μ r j := by
        have hm := μ.up_left_mem hi hj (corner_mem hc)
        rw [excess_eq hm, excess_eq (μ.up_left_mem hi le_rfl (corner_mem hc)),
          excess_eq (μ.up_left_mem le_rfl hj (corner_mem hc)), hc.1, hc.2]
        exact_mod_cast (show μ.rowLen i - (j + 1) + (μ.colLen j - (i + 1)) =
          μ.rowLen i - (s + 1) + (r + 1 - (i + 1)) +
          (s + 1 - (j + 1) + (μ.colLen j - (r + 1))) by
            have := hb.1
            have := hb'.2
            omega)
      rw [← pointWeight_step (fun k => excess μ k s) hi hb'.2 (excess_corner hc)
          (fun _ => excess_row_ne hc),
        ← pointWeight_step (excess μ r) hj hb.1 (excess_corner hc) (fun _ => excess_col_ne hc), hs]
      ring
    · rw [pointWeight_after (excess μ r) (lt_of_not_ge hj),
        sum_eq_zero (s := Ico (j + 1) (μ.rowLen i)) (f := pointWeight (excess μ r) s)
          (fun k hk => pointWeight_after _ (by have := (mem_Ico.mp hk).1; omega))]
      ring
  · rw [pointWeight_after (fun k => excess μ k s) (lt_of_not_ge hi),
      sum_eq_zero (s := Ico (i + 1) (μ.colLen j)) (f := pointWeight (fun k => excess μ k s) r)
        (fun k hk => pointWeight_after _ (by have := (mem_Ico.mp hk).1; omega))]
    ring

private theorem endpoint_at_corner {μ : YoungDiagram} {i j : ℕ} (hc : Corner μ (i, j)) :
    ∑ c ∈ corners μ, endpoint μ c i j = 1 := by
  rw [sum_eq_single (i, j)]
  · simp [endpoint, pointWeight_self]
  · rintro ⟨r, s⟩ hm hne
    have h := (mem_filter.mp hm).1
    change (r, s) ∈ μ at h
    by_cases hi : r < i
    · simp [endpoint, pointWeight_after _ hi]
    by_cases hj : s < j
    · simp [endpoint, pointWeight_after _ hj]
    have hr := YoungDiagram.mem_iff_lt_rowLen.mp (μ.up_left_mem (by omega : i ≤ r) le_rfl h)
    have hv := YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem le_rfl (by omega : j ≤ s) h)
    rw [hc.1] at hr
    rw [hc.2] at hv
    exact (hne (Prod.ext (by omega) (by omega))).elim
  · simp [corners, hc, corner_mem hc]

/-- From any initial cell the hook walk ends at some corner with total probability one. -/
private theorem endpoint_total (μ : YoungDiagram) (i j : ℕ) (hm : (i, j) ∈ μ) :
    ∑ c ∈ corners μ, endpoint μ c i j = 1 := by
  by_cases hc : Corner μ (i, j)
  · exact endpoint_at_corner hc
  have hi := YoungDiagram.mem_iff_lt_colLen.mp hm
  have hj := YoungDiagram.mem_iff_lt_rowLen.mp hm
  have hne : excess μ i j ≠ 0 := by
    rw [excess_eq hm]
    intro hz
    have he : μ.rowLen i - (j + 1) + (μ.colLen j - (i + 1)) = 0 := by exact_mod_cast hz
    apply hc
    change μ.rowLen i = j + 1 ∧ μ.colLen j = i + 1
    omega
  apply mul_left_cancel₀ hne
  rw [mul_one, mul_sum]
  calc
    _ = (∑ k ∈ Ico (i + 1) (μ.colLen j), ∑ c ∈ corners μ, endpoint μ c k j) +
        ∑ k ∈ Ico (j + 1) (μ.rowLen i), ∑ c ∈ corners μ, endpoint μ c i k := by
      simp_rw [sum_comm (s := Ico _ _)]
      rw [← sum_add_distrib]
      exact sum_congr rfl fun ⟨_, _⟩ hc => endpoint_step (mem_filter.mp hc).2 i j
    _ = _ := by
      convert_to (∑ _k ∈ Ico (i + 1) (μ.colLen j), (1 : ℚ)) +
        (∑ _k ∈ Ico (j + 1) (μ.rowLen i), (1 : ℚ)) = _
      · congr 1
        · exact sum_congr rfl fun k hk =>
            endpoint_total μ k j (YoungDiagram.mem_iff_lt_colLen.mpr (mem_Ico.mp hk).2)
        · exact sum_congr rfl fun k hk =>
            endpoint_total μ i k (YoungDiagram.mem_iff_lt_rowLen.mpr (mem_Ico.mp hk).2)
      · simp [excess_eq hm, add_comm]
termination_by hookLength μ (i, j)
decreasing_by
  all_goals
    obtain ⟨hk₁, hk₂⟩ := mem_Ico.mp hk
    first | have ha := μ.rowLen_anti i k (by omega) | have ha := μ.colLen_anti j k (by omega)
    simp only [hookLength]
    omega

private def cornerFactor (μ : YoungDiagram) (c : ℕ × ℕ) : ℚ :=
  tailWeight (fun k => excess μ k c.2) c.1 0 * tailWeight (excess μ c.1) c.2 0

private theorem sum_endpoint {μ : YoungDiagram} {r s : ℕ} (hc : Corner μ (r, s)) :
    ∑ c ∈ μ.cells, endpoint μ (r, s) c.1 c.2 = cornerFactor μ (r, s) := by
  let rect := Ico 0 (r + 1) ×ˢ Ico 0 (s + 1)
  have hsub : rect ⊆ μ.cells := by
    rintro ⟨i, j⟩ h
    obtain ⟨hi, hj⟩ := mem_product.mp h
    exact μ.up_left_mem (Nat.le_of_lt_succ (mem_Ico.mp hi).2)
      (Nat.le_of_lt_succ (mem_Ico.mp hj).2) (corner_mem hc)
  rw [← sum_subset hsub]
  · simp only [rect, sum_product, endpoint, ← mul_sum, ← sum_mul, cornerFactor]
    rw [sum_pointWeight _ (Nat.zero_le r) (Nat.lt_succ_self r),
      sum_pointWeight _ (Nat.zero_le s) (Nat.lt_succ_self s)]
  · rintro ⟨i, j⟩ _ h
    by_cases hi : r < i
    · simp [endpoint, pointWeight_after _ hi]
    · have hj : s < j := by
        contrapose! h
        exact mem_product.mpr ⟨mem_Ico.mpr ⟨by omega, by omega⟩, mem_Ico.mpr ⟨by omega, by omega⟩⟩
      simp [endpoint, pointWeight_after _ hj]

private theorem sum_cornerFactor (μ : YoungDiagram) :
    ∑ c ∈ corners μ, cornerFactor μ c = (μ.card : ℚ) := by
  calc
    _ = ∑ c ∈ corners μ, ∑ p ∈ μ.cells, endpoint μ c p.1 p.2 :=
      sum_congr rfl fun ⟨_, _⟩ hc => (sum_endpoint (mem_filter.mp hc).2).symm
    _ = ∑ p ∈ μ.cells, ∑ c ∈ corners μ, endpoint μ c p.1 p.2 := sum_comm
    _ = ∑ _ ∈ μ.cells, (1 : ℚ) := sum_congr rfl fun ⟨_, _⟩ hp => endpoint_total μ _ _ hp
    _ = _ := by simp

private def hookProduct (μ : YoungDiagram) : ℚ := ∏ p ∈ μ.cells, (hookLength μ p : ℚ)

private theorem lengths_erase {μ ν : YoungDiagram} {r s : ℕ} (hc : Corner μ (r, s))
    (he : ν.cells = μ.cells.erase (r, s)) (i j : ℕ) :
    ν.rowLen i = (if i = r then s else μ.rowLen i) ∧
    ν.colLen j = (if j = s then r else μ.colLen j) := by
  have hm (a b : ℕ) : (a, b) ∈ ν ↔ (a ≠ r ∨ b ≠ s) ∧ (a, b) ∈ μ := by
    change (a, b) ∈ ν.cells ↔ _
    simp only [he, mem_erase, ne_eq, Prod.mk.injEq, not_and_or, YoungDiagram.mem_cells]
  constructor
  · apply eq_of_forall_lt_iff
    intro k
    rw [← YoungDiagram.mem_iff_lt_rowLen, hm, YoungDiagram.mem_iff_lt_rowLen]
    split_ifs with hi
    · subst i
      rw [hc.1]
      omega
    · simp [hi]
  · apply eq_of_forall_lt_iff
    intro k
    rw [← YoungDiagram.mem_iff_lt_colLen, hm, YoungDiagram.mem_iff_lt_colLen]
    split_ifs with hj
    · subst j
      rw [hc.2]
      omega
    · simp [hj]

private theorem adjust_hook {a b : ℕ} (h : a = b + 1) (hb : 0 < b) :
    (a : ℚ) = b * (1 + ((a : ℚ) - 1)⁻¹) := by
  rw [h, Nat.cast_add_one]
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  simp [mul_add, hb']

/-- Deleting a corner shortens precisely the hooks above it and to its left.
Their multiplicative changes are the two factors of the endpoint weight. -/
private theorem hookProduct_erase {μ ν : YoungDiagram} {r s : ℕ} (hc : Corner μ (r, s))
    (he : ν.cells = μ.cells.erase (r, s)) :
    hookProduct μ = hookProduct ν * cornerFactor μ (r, s) := by
  let above := Ico 0 r ×ˢ {s}
  let left := {r} ×ˢ Ico 0 s
  have ha : above ⊆ ν.cells := by
    rintro ⟨i, j⟩ hp
    obtain ⟨hi, hj⟩ := mem_product.mp hp
    obtain rfl : j = s := mem_singleton.mp hj
    have hi' : i < r := (mem_Ico.mp hi).2
    exact he ▸ mem_erase.mpr ⟨by simp [hi'.ne], μ.up_left_mem hi'.le le_rfl (corner_mem hc)⟩
  have hl : left ⊆ ν.cells := by
    rintro ⟨i, j⟩ hp
    obtain ⟨hi, hj⟩ := mem_product.mp hp
    obtain rfl : i = r := mem_singleton.mp hi
    have hj' : j < s := (mem_Ico.mp hj).2
    exact he ▸ mem_erase.mpr ⟨by simp [hj'.ne], μ.up_left_mem le_rfl hj'.le (corner_mem hc)⟩
  let factor (t : Finset (ℕ × ℕ)) (p : ℕ × ℕ) :=
    if p ∈ t then 1 + (excess μ p.1 p.2)⁻¹ else 1
  have hpoint (p : ℕ × ℕ) (hp : p ∈ ν.cells) : (hookLength μ p : ℚ) =
      (hookLength ν p : ℚ) * (factor above p * factor left p) := by
    obtain ⟨i, j⟩ := p
    have hpos := hookLength_pos (show (i, j) ∈ ν from hp)
    have hr := YoungDiagram.mem_iff_lt_rowLen.mp (show (i, j) ∈ ν from hp)
    have hv := YoungDiagram.mem_iff_lt_colLen.mp (show (i, j) ∈ ν from hp)
    obtain ⟨hr', hv'⟩ := lengths_erase hc he i j
    by_cases hi : i = r <;> by_cases hj : j = s
    · subst i
      subst j
      simp [he] at hp
    · subst i
      have hjlt : j < s := by simpa [hr'] using hr
      simp only [factor, above, left, mem_product, mem_singleton, mem_Ico, zero_le, true_and,
        hj, and_false, ite_false, hjlt, and_self, ite_true, one_mul, excess]
      apply adjust_hook _ hpos
      simp only [hookLength, hr', hv', hj, ite_false, hc.1, ite_true]
      omega
    · subst j
      have hilt : i < r := by simpa [hv'] using hv
      simp only [factor, above, left, mem_product, mem_singleton, mem_Ico, zero_le, true_and,
        hi, false_and, ite_false, hilt, and_self, ite_true, mul_one, excess]
      apply adjust_hook _ hpos
      simp only [hookLength, hr', hv', hi, ite_false, hc.2, ite_true]
      omega
    · simp [factor, above, left, hi, hj, Ne.symm hi, Ne.symm hj, hookLength, hr', hv']
  have hsingle : (hookLength μ (r, s) : ℚ) = 1 := sub_eq_zero.mp (excess_corner hc)
  have hprod (t : Finset (ℕ × ℕ)) (ht : t ⊆ ν.cells) :
      ∏ p ∈ ν.cells, factor t p = ∏ p ∈ t, (1 + (excess μ p.1 p.2)⁻¹) := by
    rw [show (∏ p ∈ ν.cells, factor t p) = _ from prod_ite_mem _ _ _, inter_eq_right.mpr ht]
  calc
    _ = ∏ p ∈ ν.cells, (hookLength μ p : ℚ) := by
      simpa only [hookProduct, he, hsingle, mul_one] using
        (prod_erase_mul μ.cells (fun p => (hookLength μ p : ℚ)) (corner_mem hc)).symm
    _ = _ := by
      rw [prod_congr rfl hpoint, prod_mul_distrib, prod_mul_distrib, hprod above ha, hprod left hl]
      simp [above, left, hookProduct, cornerFactor, tailWeight]

/-- A removable row corresponds to the corner at its right end. -/
private def cornerRows (μ : YoungDiagram) : ↥(corners μ) ≃ RemoveRow μ where
  toFun c := ⟨c.val.1, by
    obtain ⟨⟨r, s⟩, hm⟩ := c
    have h := (mem_filter.mp hm).2
    have hnext : (r + 1, s) ∉ μ := by
      rw [YoungDiagram.mem_iff_lt_colLen, h.2]
      exact lt_irrefl _
    rw [YoungDiagram.mem_iff_lt_rowLen] at hnext
    change μ.rowLen (r + 1) < μ.rowLen r
    rw [h.1]
    omega⟩
  invFun i := by
    let s := μ.rowLen i - 1
    have hdrop := i.property
    have hr : μ.rowLen i = s + 1 := by dsimp [s]; omega
    have hm : (i.val, s) ∈ μ := YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
    have hn : (i.val + 1, s) ∉ μ := by
      rw [YoungDiagram.mem_iff_lt_rowLen]
      omega
    rw [YoungDiagram.mem_iff_lt_colLen] at hn
    have hv := YoungDiagram.mem_iff_lt_colLen.mp hm
    exact ⟨(i.val, s), mem_filter.mpr ⟨hm, hr, by dsimp; omega⟩⟩
  left_inv := by
    rintro ⟨⟨r, s⟩, hm⟩
    apply Subtype.ext
    change (r, μ.rowLen r - 1) = (r, s)
    rw [(mem_filter.mp hm).2.1]
    simp
  right_inv _ := rfl

private def predecessor (μ : YoungDiagram) (c : ↥(corners μ)) : Lower μ :=
  removeCell μ (cornerRows μ c)

private theorem predecessor_cells {μ : YoungDiagram} (c : ↥(corners μ)) :
    (predecessor μ c).val.cells = μ.cells.erase c.val := by
  obtain ⟨⟨r, s⟩, hm⟩ := c
  change μ.cells.erase (r, μ.rowLen r - 1) = μ.cells.erase (r, s)
  rw [(mem_filter.mp hm).2.1]
  simp

private theorem count_predecessors {n : ℕ} (μ : YoungDiagram) (hn : μ.card = n + 1) :
    sytCount μ = ∑ c : ↥(corners μ), sytCount (predecessor μ c).val := by
  classical
  let _ := shapeFintype n
  let shape : Shape (n + 1) := ⟨μ, hn⟩
  let e := (cornerRows μ).trans ((Equiv.ofBijective (removeCell μ)
    (removeCell_bijective μ)).trans (lowerEquiv shape).symm)
  calc
    sytCount μ = ∑ ν : {ν : Shape n // ν.val ≤ μ}, sytCount ν.val.val :=
      (Nat.card_congr (tableauEquivPredecessors shape).symm).trans Nat.card_sigma
    _ = _ := (e.sum_comp (fun ν => sytCount ν.val.val)).symm

private theorem count_mul_hooks (μ : YoungDiagram) :
    (sytCount μ : ℚ) * hookProduct μ = μ.card.factorial := by
  induction h : μ.card generalizing μ with
  | zero => simp [eq_bot_of_card_zero h, sytCount_bot, hookProduct]
  | succ n ih =>
    have hterm (c : ↥(corners μ)) :
        (sytCount (predecessor μ c).val : ℚ) * hookProduct μ =
          n.factorial * cornerFactor μ c.val := by
      let ν := (predecessor μ c).val
      have hν : ν.card = n := Nat.add_right_cancel ((predecessor μ c).property.2.trans h)
      obtain ⟨⟨r, s⟩, hc⟩ := c
      rw [hookProduct_erase (mem_filter.mp hc).2 (predecessor_cells (μ := μ) ⟨(r, s), hc⟩),
        ← mul_assoc]
      exact congrArg (· * _) (ih ν hν)
    calc
      _ = ∑ c : ↥(corners μ), (sytCount (predecessor μ c).val : ℚ) * hookProduct μ := by
        rw [count_predecessors μ h, Nat.cast_sum, sum_mul]
      _ = ∑ c : ↥(corners μ), n.factorial * cornerFactor μ c.val :=
        sum_congr rfl fun c _ => hterm c
      _ = _ := by
        rw [← mul_sum, sum_coe_sort, sum_cornerFactor, h, Nat.factorial_succ, Nat.cast_mul]
        ring

/-- **Hook length formula.** For a partition `λ ⊢ n`, the number of standard Young tableaux of
shape `λ` is `f^λ = n! / ∏_{u ∈ λ} h(u)`, the product running over the cells `u` of the diagram
of `λ` and `h(u)` the hook length; stated here with the denominator cleared (Stanley, *Topics in
Algebraic Combinatorics*, author's draft of 1 February 2013, Theorem 8.1). -/
theorem sytCount_mul_prod_hookLength (μ : YoungDiagram) :
    sytCount μ * ∏ c ∈ μ.cells, hookLength μ c = μ.card.factorial := by
  exact_mod_cast (show (sytCount μ : ℚ) * ∏ c ∈ μ.cells, (hookLength μ c : ℚ) =
    μ.card.factorial from count_mul_hooks μ)

end MathlibExt.Combinatorics.YoungTableaux.HookLengthWanted
