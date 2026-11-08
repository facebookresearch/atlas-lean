/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Geometry.ClosestPair
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.List.TakeWhile
public import Cslib.Algorithms.Lean.MergeSort.MergeSort

/-!
# Closest pair: the `O(n log n)` bound

CLRS, third edition, Section 33.4, the running-time analysis of the closest-pair algorithm in
`CSLibExt.Algorithms.Lean.Geometry.ClosestPair`: in the strip, each point is compared with at most
seven following points, so a call on `n` points does `O(n)` work besides the recursion and the
whole algorithm computes `O(n lg n)` distances.

The packing argument (`length_le_seven`): the points compared with `p` lie, together with `p`, in
the `2δ × δ` rectangle above `p` around the dividing line (`δ` the distance, here `√δ₂` for the
squared distance `δ₂`). Split it into eight `δ/2 × δ/2` squares, four on each side of the line.
Two points of the same half in one square are closer than `δ`, impossible since `δ` is at most the
closest-pair distance within each half; so the rectangle holds at most eight points.

The strip points carry their side for the argument only (the algorithm does not change): sorting
the side-tagged strip and forgetting the tags is the same as sorting the strip
(`List.map_mergeSort`).

* `stripScan_time_le`: a sorted strip of `m` points costs at most `7 m`.
* `closestRec_time_le`, `closestPair_time_le`: at most `7 n ⌈log₂ n⌉ + n` distances on `n` points.

Distances are real here because the packing argument uses `√δ₂`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Geometry

open Cslib.Algorithms.Lean TimeM
open Cslib.Algorithms.Lean.SparseTable (omin)
open scoped List

/-- A strip point with its side of the dividing line (`false` left, `true` right). -/
abbrev Tagged := (ℝ × ℝ) × Bool

/-- Two points of the same side are at squared distance at least `δ`. -/
def SameSideFar (δ : ℝ) (a b : Tagged) : Prop := a.2 = b.2 → δ ≤ dist2 a.1 b.1

/-- A strip point: within squared distance `δ` of the line `x = xmid`, on its own side. -/
def InStrip (δ xmid : ℝ) (a : Tagged) : Prop :=
  (a.1.1 - xmid) ^ 2 < δ ∧ (a.2 = false → a.1.1 ≤ xmid) ∧ (a.2 = true → xmid ≤ a.1.1)

theorem SameSideFar.symm {δ : ℝ} {a b : Tagged} (h : SameSideFar δ a b) : SameSideFar δ b a :=
  fun hab => by rw [dist2_comm]; exact h hab.symm

/-! ## Packing -/

/-- Two points of the same side in the same `s/2`-square of the rectangle are at squared distance
at most `s² / 2`. -/
private theorem dist2_le_of_same_cell {s xmid y₀ : ℝ} {a b : Tagged}
    (ha : |a.1.1 - xmid| < s) (hb : |b.1.1 - xmid| < s) (hside : a.2 = b.2)
    (haL : a.2 = false → a.1.1 ≤ xmid) (haR : a.2 = true → xmid ≤ a.1.1)
    (hbL : b.2 = false → b.1.1 ≤ xmid) (hbR : b.2 = true → xmid ≤ b.1.1)
    (hya : 0 ≤ a.1.2 - y₀ ∧ a.1.2 - y₀ < s) (hyb : 0 ≤ b.1.2 - y₀ ∧ b.1.2 - y₀ < s)
    (hcx : |a.1.1 - xmid| ≤ s / 2 ↔ |b.1.1 - xmid| ≤ s / 2)
    (hcy : a.1.2 - y₀ ≤ s / 2 ↔ b.1.2 - y₀ ≤ s / 2) :
    dist2 a.1 b.1 ≤ s ^ 2 / 2 := by
  have hx : |a.1.1 - b.1.1| ≤ s / 2 := by
    rw [abs_lt] at ha hb
    rcases Bool.eq_false_or_eq_true a.2 with h | h
    · have h1 := haR h
      have h2 := hbR (hside ▸ h)
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hcx
      rw [abs_le]
      by_cases hn : a.1.1 - xmid ≤ s / 2
      · have := hcx.1 hn
        constructor <;> linarith
      · have := mt hcx.2 hn
        constructor <;> linarith
    · have h1 := haL h
      have h2 := hbL (hside ▸ h)
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at hcx
      rw [abs_le]
      by_cases hn : -(a.1.1 - xmid) ≤ s / 2
      · have := hcx.1 hn
        constructor <;> linarith
      · have := mt hcx.2 hn
        constructor <;> linarith
  have hy : |a.1.2 - b.1.2| ≤ s / 2 := by
    rw [abs_le]
    by_cases hn : a.1.2 - y₀ ≤ s / 2
    · have := hcy.1 hn
      constructor <;> linarith
    · have := mt hcy.2 hn
      constructor <;> linarith
  have hx2 : (a.1.1 - b.1.1) ^ 2 ≤ (s / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hy2 : (a.1.2 - b.1.2) ^ 2 ≤ (s / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
  simp only [dist2]
  nlinarith

/-- CLRS's packing bound: at most seven strip points follow `p` within `y` gap `√δ`. -/
theorem length_le_seven {δ xmid : ℝ} (p : Tagged) (Z : List Tagged)
    (hpair : (p :: Z).Pairwise (SameSideFar δ))
    (hstrip : ∀ a ∈ p :: Z, InStrip δ xmid a)
    (hy : ∀ a ∈ Z, p.1.2 ≤ a.1.2 ∧ (a.1.2 - p.1.2) ^ 2 < δ) :
    Z.length ≤ 7 := by
  by_contra hlen
  have hδ : 0 < δ := lt_of_le_of_lt (sq_nonneg _) (hstrip p List.mem_cons_self).1
  set s := √δ with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hδ
  have hss : s ^ 2 = δ := Real.sq_sqrt hδ.le
  -- every point is in the rectangle
  have hbox : ∀ a ∈ p :: Z, |a.1.1 - xmid| < s ∧ 0 ≤ a.1.2 - p.1.2 ∧ a.1.2 - p.1.2 < s := by
    intro a ha
    refine ⟨(Real.lt_sqrt (abs_nonneg _)).2 (by rw [sq_abs]; exact (hstrip a ha).1), ?_⟩
    rcases List.mem_cons.1 ha with rfl | ha
    · simp [hs0]
    · obtain ⟨h1, h2⟩ := hy a ha
      refine ⟨by linarith, ?_⟩
      have := (Real.lt_sqrt (abs_nonneg _)).2 (by rw [sq_abs]; exact h2)
      rwa [abs_of_nonneg (by linarith)] at this
  -- eight cells
  let L := p :: Z
  let cell : Fin L.length → Bool × Bool × Bool := fun i =>
    (L[i].2, decide (|L[i].1.1 - xmid| ≤ s / 2), decide (L[i].1.2 - p.1.2 ≤ s / 2))
  have hcard : Fintype.card (Bool × Bool × Bool) < Fintype.card (Fin L.length) := by
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, L, List.length_cons]
    omega
  obtain ⟨i, j, hij, hcell⟩ := Fintype.exists_ne_map_eq_of_card_lt cell hcard
  have hpw := List.pairwise_iff_getElem.1 hpair
  -- the two points in one cell
  have key : ∀ i j : Fin L.length, i < j → cell i = cell j → False := by
    intro i j hlt hc
    simp only [cell, Prod.mk.injEq, decide_eq_decide] at hc
    obtain ⟨hside, hcx, hcy⟩ := hc
    have hfar := hpw i j i.isLt j.isLt hlt hside
    have hai : L[i] ∈ L := List.getElem_mem _
    have haj : L[j] ∈ L := List.getElem_mem _
    obtain ⟨hxi, hyi0, hyi1⟩ := hbox _ hai
    obtain ⟨hxj, hyj0, hyj1⟩ := hbox _ haj
    have hsi := hstrip _ hai
    have hsj := hstrip _ haj
    have hle := dist2_le_of_same_cell hxi hxj hside hsi.2.1 hsi.2.2 hsj.2.1 hsj.2.2
      ⟨hyi0, hyi1⟩ ⟨hyj0, hyj1⟩ hcx hcy
    rw [hss] at hle
    have hfar' : δ ≤ dist2 L[i].1 L[j].1 := hfar
    linarith
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hcell
  · exact key j i h hcell.symm

/-! ## The strip scan -/

theorem scanFrom_time (δ : ℝ) (q : ℝ × ℝ) (L : List (ℝ × ℝ)) :
    (scanFrom δ q L).time = (L.takeWhile fun r => decide ((r.2 - q.2) ^ 2 < δ)).length := by
  induction L with
  | nil => rfl
  | cons r L ih =>
      by_cases h : (r.2 - q.2) ^ 2 < δ
      · simp only [scanFrom, h, ite_true, time_bind, time_tick, time_pure, ih,
          List.takeWhile_cons, decide_true, List.length_cons]
        omega
      · simp [scanFrom, h]

/-- A strip sorted by `y` whose same-side points are `δ` apart costs at most `7` per point. -/
theorem stripScan_time_le (δ xmid : ℝ) (Y : List Tagged)
    (hsorted : Y.Pairwise fun a b => a.1.2 ≤ b.1.2) (hpair : Y.Pairwise (SameSideFar δ))
    (hstrip : ∀ a ∈ Y, InStrip δ xmid a) :
    (stripScan δ (Y.map Prod.fst)).time ≤ 7 * Y.length := by
  induction Y with
  | nil => simp [stripScan]
  | cons p rest ih =>
      simp only [List.map_cons, stripScan, time_bind, time_pure, Nat.add_zero, List.length_cons]
      have hrun : (scanFrom δ p.1 (rest.map Prod.fst)).time ≤ 7 := by
        rw [scanFrom_time, List.takeWhile_map, List.length_map]
        set Z := rest.takeWhile ((fun r : ℝ × ℝ => decide ((r.2 - p.1.2) ^ 2 < δ)) ∘ Prod.fst)
        have hZ : Z <+ rest := List.takeWhile_sublist _
        refine length_le_seven p Z (hpair.sublist (hZ.cons_cons p))
          (fun a ha => hstrip a ((hZ.cons_cons p).subset ha)) (fun a ha => ⟨?_, ?_⟩)
        · exact List.rel_of_pairwise_cons hsorted (hZ.subset ha)
        · simpa using List.mem_takeWhile_imp ha
      have := ih hsorted.of_cons hpair.of_cons (fun a ha => hstrip a (List.mem_cons_of_mem _ ha))
      omega

/-! ## The recursion -/

private theorem omin_some_le_left {a c : ℝ} {b : Option ℝ} (h : omin (some a) b = some c) :
    c ≤ a := by
  cases b with
  | none =>
      simp only [omin, Option.some.injEq] at h
      exact h ▸ le_rfl
  | some b =>
      simp only [omin, Option.some.injEq] at h
      exact h ▸ min_le_left a b

private theorem omin_some_le_right {b c : ℝ} {a : Option ℝ} (h : omin a (some b) = some c) :
    c ≤ b := by
  cases a with
  | none =>
      simp only [omin, Option.some.injEq] at h
      exact h ▸ le_rfl
  | some a =>
      simp only [omin, Option.some.injEq] at h
      exact h ▸ min_le_right a b

/-- On `n` points sorted by `x`, the recursion computes at most `7 n ⌈log₂ n⌉ + n` distances. -/
theorem closestRec_time_le (xs : List (ℝ × ℝ)) (hs : xs.Pairwise fun a b => a.1 ≤ b.1) :
    (closestRec xs).time ≤ 7 * xs.length * Nat.clog 2 xs.length + xs.length := by
  induction h : xs.length using Nat.strong_induction_on generalizing xs with
  | _ n ih =>
    rw [closestRec]
    split_ifs with hle
    · have hb := bruteMin_time xs
      rw [h] at hb hle
      have : (bruteMin xs).time ≤ n := by
        obtain h0 | h0 | h0 | h0 : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
        all_goals subst h0; omega
      exact this.trans (Nat.le_add_left _ _)
    · simp only [time_bind]
      have hLR : xs.take (xs.length / 2) ++ xs.drop (xs.length / 2) = xs :=
        List.take_append_drop _ _
      have hLlen : (xs.take (xs.length / 2)).length = xs.length / 2 := by
        simp only [List.length_take]; omega
      have hRlen : (xs.drop (xs.length / 2)).length = xs.length - xs.length / 2 :=
        List.length_drop
      generalize xs.take (xs.length / 2) = L at hLR hLlen ⊢
      generalize xs.drop (xs.length / 2) = R at hLR hRlen ⊢
      have hsLR : (L ++ R).Pairwise fun a b => a.1 ≤ b.1 := by rw [hLR]; exact hs
      have hLsub : L <+ xs := hLR ▸ List.sublist_append_left L R
      have hRsub : R <+ xs := hLR ▸ List.sublist_append_right L R
      have ihL := ih L.length (by omega) L (hs.sublist hLsub) rfl
      have ihR := ih R.length (by omega) R (hs.sublist hRsub) rfl
      have ansL := closestRec_isAnswer L (hs.sublist hLsub)
      have ansR := closestRec_isAnswer R (hs.sublist hRsub)
      obtain ⟨δ, hδ⟩ : ∃ δ, omin (closestRec L).ret (closestRec R).ret = some δ := by
        match R, hRlen, ansR with
        | a :: b :: rest, _, ansR =>
            obtain ⟨d, hd, -⟩ := ansR.lower a b (by simp)
            rw [hd]
            cases (closestRec L).ret with
            | none => exact ⟨d, rfl⟩
            | some l => exact ⟨min l d, rfl⟩
        | [], h, _ => simp at h; omega
        | [_], h, _ => simp at h; omega
      rw [hδ]
      simp only [time_bind, time_pure, Nat.add_zero]
      -- both halves are `δ`-separated
      have hδL : ∀ a b, [a, b] <+ L → δ ≤ dist2 a b := fun a b hab => by
        obtain ⟨d, hd, hle⟩ := ansL.lower a b hab
        rw [hd] at hδ
        exact (omin_some_le_left hδ).trans hle
      have hδR : ∀ a b, [a, b] <+ R → δ ≤ dist2 a b := fun a b hab => by
        obtain ⟨d, hd, hle⟩ := ansR.lower a b hab
        rw [hd] at hδ
        exact (omin_some_le_right hδ).trans hle
      -- the dividing line
      obtain ⟨L', l, hLl⟩ : ∃ L' l, L = L' ++ [l] := by
        rcases List.eq_nil_or_concat L with hL0 | ⟨L', l, hL'⟩
        · rw [hL0] at hLlen; simp at hLlen; omega
        · exact ⟨L', l, by rw [hL', List.concat_eq_append]⟩
      have hxmid : (Option.map Prod.fst L.getLast?).getD 0 = l.1 := by simp [hLl]
      rw [hxmid]
      have hleft : ∀ q ∈ L, q.1 ≤ l.1 := fun q hq => by
        have hs' := hsLR
        rw [hLl] at hq hs'
        rcases List.mem_append.1 hq with h | h
        · exact (List.pairwise_append.1 (List.pairwise_append.1 hs').1).2.2 q h l
            List.mem_cons_self
        · rw [List.mem_singleton.1 h]
      have hright : ∀ q ∈ R, l.1 ≤ q.1 := fun q hq =>
        (List.pairwise_append.1 hsLR).2.2 l (by rw [hLl]; simp) q hq
      -- the side-tagged strip
      set f : ℝ × ℝ → Bool := fun p => decide ((p.1 - l.1) ^ 2 < δ) with hf
      let tagged : List Tagged := (L.filter f).map (·, false) ++ (R.filter f).map (·, true)
      have hstripeq : xs.filter f = tagged.map Prod.fst := by
        rw [← hLR, List.filter_append]
        simp [tagged, List.map_append, List.map_map, Function.comp_def]
      have hys : (xs.filter f).mergeSort (fun a b => decide (a.2 ≤ b.2)) =
          (tagged.mergeSort fun a b => decide (a.1.2 ≤ b.1.2)).map Prod.fst := by
        rw [hstripeq]
        exact (List.map_mergeSort (r := fun a b => decide (a.1.2 ≤ b.1.2))
          (s := fun a b => decide (a.2 ≤ b.2)) (f := Prod.fst) (l := tagged)
          (fun _ _ _ _ => rfl)).symm
      rw [hys]
      set Y := tagged.mergeSort fun a b => decide (a.1.2 ≤ b.1.2) with hY
      have hperm : Y ~ tagged := List.mergeSort_perm _ _
      have hsorted : Y.Pairwise fun a b => a.1.2 ≤ b.1.2 :=
        (List.pairwise_mergeSort (le := fun a b => decide (a.1.2 ≤ b.1.2))
          (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; exact hab.trans hbc)
          (fun a b => by simpa using le_total a.1.2 b.1.2) tagged).imp (fun h => by simpa using h)
      have htagged : tagged.Pairwise (SameSideFar δ) := by
        refine List.pairwise_append.2 ⟨?_, ?_, ?_⟩
        · rw [List.pairwise_map, List.pairwise_iff_forall_sublist]
          exact fun hab _ => hδL _ _ (hab.trans List.filter_sublist)
        · rw [List.pairwise_map, List.pairwise_iff_forall_sublist]
          exact fun hab _ => hδR _ _ (hab.trans List.filter_sublist)
        · intro a ha b hb hab
          simp only [List.mem_map] at ha hb
          obtain ⟨_, -, rfl⟩ := ha
          obtain ⟨_, -, rfl⟩ := hb
          simp at hab
      have hpair : Y.Pairwise (SameSideFar δ) :=
        (hperm.pairwise_iff fun h => SameSideFar.symm h).2 htagged
      have hstrip : ∀ a ∈ Y, InStrip δ l.1 a := fun a ha => by
        rcases List.mem_append.1 (hperm.subset ha) with h | h
        · simp only [List.mem_map, List.mem_filter] at h
          obtain ⟨q, ⟨hqL, hqf⟩, rfl⟩ := h
          exact ⟨by simpa [hf] using hqf, fun _ => hleft q hqL, fun h => by simp at h⟩
        · simp only [List.mem_map, List.mem_filter] at h
          obtain ⟨q, ⟨hqR, hqf⟩, rfl⟩ := h
          exact ⟨by simpa [hf] using hqf, fun h => by simp at h, fun _ => hright q hqR⟩
      have hscan := stripScan_time_le δ l.1 Y hsorted hpair hstrip
      have hYlen : Y.length ≤ n := by
        rw [hperm.length_eq]
        simp only [tagged, List.length_append, List.length_map]
        have := List.length_filter_le f L
        have := List.length_filter_le f R
        omega
      -- the recurrence
      rw [hLlen] at ihL
      rw [hRlen] at ihR
      have hc1 : 1 ≤ Nat.clog 2 n := Nat.succ_le_of_lt (Nat.clog_pos (by decide) (by omega))
      have hca : Nat.clog 2 (n / 2) ≤ Nat.clog 2 n - 1 := clog2_floor_half_le n (by omega)
      have hcb : Nat.clog 2 (n - n / 2) ≤ Nat.clog 2 n - 1 := by
        have := clog2_half_le n (by omega)
        rwa [show n - n / 2 = (n + 1) / 2 by omega]
      rw [h] at ihL ihR
      set c := Nat.clog 2 n
      set a := n / 2
      set b := n - n / 2
      have h1 : a * Nat.clog 2 a ≤ a * (c - 1) := Nat.mul_le_mul_left _ hca
      have h2 : b * Nat.clog 2 b ≤ b * (c - 1) := Nat.mul_le_mul_left _ hcb
      have h3 : a * (c - 1) + b * (c - 1) = n * (c - 1) := by
        rw [← Nat.add_mul]; congr 1; omega
      have h4 : n * (c - 1) + n = n * c := by
        conv_rhs => rw [show c = (c - 1) + 1 by omega]
        rw [Nat.mul_add, Nat.mul_one]
      have e1 : 7 * a * Nat.clog 2 a = 7 * (a * Nat.clog 2 a) := Nat.mul_assoc _ _ _
      have e2 : 7 * b * Nat.clog 2 b = 7 * (b * Nat.clog 2 b) := Nat.mul_assoc _ _ _
      have e3 : 7 * n * c = 7 * (n * c) := Nat.mul_assoc _ _ _
      omega

/-- CLRS Section 33.4: the closest-pair algorithm computes `O(n lg n)` distances, at most
`7 n ⌈log₂ n⌉ + n` on `n` points. -/
theorem closestPair_time_le (ps : List (ℝ × ℝ)) :
    (closestPair ps).time ≤ 7 * ps.length * Nat.clog 2 ps.length + ps.length := by
  have hsorted : (ps.mergeSort fun a b => decide (a.1 ≤ b.1)).Pairwise fun a b => a.1 ≤ b.1 :=
    (List.pairwise_mergeSort (le := fun a b => decide (a.1 ≤ b.1))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at hab hbc ⊢; exact hab.trans hbc)
      (fun a b => by simpa using le_total a.1 b.1) ps).imp (fun h => by simpa using h)
  have := closestRec_time_le _ hsorted
  rwa [List.length_mergeSort] at this

end Cslib.Algorithms.Lean.Geometry
