/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Hull
public import MathlibExt.NumberTheory.ShadowMarkoffTree
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# The polygon of nonnegative shadow Markoff trees

`exists_polygon_shadowMarkoffTree_nonneg_iff` characterizes the nonnegative trees
by the cone over a rational quadrilateral. Besides nonnegativity of the initial triple
`(α, β, γ)`, the two inequalities are `2 * α ≤ β + γ` and `α + β ≤ 2 * γ`.
On the slice `α + β + γ = 3`, the vertices are `(0,0,3)`, `(0,2,1)`, `(1,0,2)` and `(1,1,1)`.

The proof uses the mutation recurrence in dual numbers. On a branch with one coordinate fixed,
a negative rescaled shadow at that coordinate forces the ratio of shadow to classical part
to become arbitrarily negative.
-/

namespace MetaMathlibExt

namespace ShadowMarkoffPolygon

private abbrev State := (Fin 3 → ℚ) × (Fin 3 → ℚ)

private def raw (s : State) (i : Fin 3) : DualNumber ℚ := (s.1 i, s.2 i)

private def factor (σ : ℚ) : DualNumber ℚ := (3, -σ)

-- Multiplication by 3 - σε changes the Markoff equation into A² + B² + C² = ABC.
private def coord (σ : ℚ) (s : State) (i : Fin 3) : DualNumber ℚ :=
  factor σ * raw s i

private def Distinct (i j k : Fin 3) := i ≠ j ∧ i ≠ k ∧ j ≠ k

private lemma third_index {i k : Fin 3} (h : i ≠ k) : ∃ j, Distinct i j k := by
  revert i k
  unfold Distinct
  decide

private lemma univ_triple {i j k : Fin 3} (h : Distinct i j k) :
    Finset.univ = {i, j, k} := by
  ext t
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  revert i j k t
  unfold Distinct
  decide

private def Markoff (f : Fin 3 → DualNumber ℚ) :=
  ∑ i, f i ^ 2 = ∏ i, f i

private lemma markoff_iff {f : Fin 3 → DualNumber ℚ} {i j k : Fin 3} (h : Distinct i j k) :
    Markoff f ↔ f i ^ 2 + f j ^ 2 + f k ^ 2 = f i * f j * f k := by
  simp [Markoff, univ_triple h, h.1, h.2.1, h.2.2, add_assoc, mul_assoc]

private lemma sum_other (f : Fin 3 → ℚ) {i j k : Fin 3} (h : Distinct i j k) :
    ∑ t ∈ Finset.univ.erase i, f t = f j + f k := by
  simp [univ_triple h, h.1, h.2.1, h.2.2]

private lemma coord_mutate_ne {σ : ℚ} {s : State} {i j : Fin 3} (h : j ≠ i) :
    coord σ (shadowMarkoffMutate i s) j = coord σ s j := by
  simp [coord, raw, shadowMarkoffMutate, h]

private lemma mutate_formula {σ : ℚ} {s : State} {i j k : Fin 3} (h : Distinct i j k)
    (hm : Markoff (coord σ s)) (hi : 0 < (coord σ s i).fst) :
    coord σ (shadowMarkoffMutate i s) i = coord σ s j * coord σ s k - coord σ s i := by
  have ha : s.1 i ≠ 0 := by
    change 0 < 3 * s.1 i at hi
    exact ne_of_gt (by linarith)
  have product : raw (shadowMarkoffMutate i s) i * raw s i = raw s j ^ 2 + raw s k ^ 2 := by
    let s' := shadowMarkoffMutate i s
    apply TrivSqZeroExt.ext
    · change s'.1 i * s.1 i = s.1 j ^ 2 + s.1 k ^ 2
      simp [s', shadowMarkoffMutate, sum_other _ h, ha]
    · rw [pow_two, pow_two]
      change s'.1 i * s.2 i + s'.2 i * s.1 i =
        (s.1 j * s.2 j + s.2 j * s.1 j) + (s.1 k * s.2 k + s.2 k * s.1 k)
      simp [s', shadowMarkoffMutate, sum_other _ h, ha]
      ring
  have scaled : coord σ (shadowMarkoffMutate i s) i * coord σ s i =
      coord σ s j ^ 2 + coord σ s k ^ 2 := by
    unfold coord
    linear_combination factor σ ^ 2 * product
  have unit : IsUnit (coord σ s i) :=
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hi.ne')
  apply unit.mul_left_inj.mp
  linear_combination scaled + (markoff_iff h).mp hm

private lemma markoff_mutate {σ : ℚ} {s : State} {i j k : Fin 3} (h : Distinct i j k)
    (hm : Markoff (coord σ s)) (hi : 0 < (coord σ s i).fst) :
    Markoff (coord σ (shadowMarkoffMutate i s)) := by
  rw [markoff_iff h, mutate_formula h hm hi, coord_mutate_ne h.1.symm,
    coord_mutate_ne h.2.1.symm]
  linear_combination (markoff_iff h).mp hm

private def liftTriple (v : Fin 3 → ℤ) (i : Fin 3) : ℚ := v i

private def weight (v : Fin 3 → ℤ) : ℚ := liftTriple v 0 + liftTriple v 1 + liftTriple v 2

private abbrev first (v : Fin 3 → ℤ) := shadowMarkoffMutate 0 (shadowMarkoffRoot v)

private abbrev start (v : Fin 3 → ℤ) := shadowMarkoffMutate 1 (first v)

private lemma first_eq (v : Fin 3 → ℤ) :
    first v = (![2, 1, 1], ![-2 * liftTriple v 0 + 2 * liftTriple v 1 + 2 * liftTriple v 2,
      liftTriple v 1, liftTriple v 2]) := by
  ext i <;> fin_cases i <;>
    simp [first, shadowMarkoffRoot, shadowMarkoffMutate, liftTriple, Function.update,
      Finset.sum_erase_eq_sub, Fin.sum_univ_three]
  ring

private lemma start_eq (v : Fin 3 → ℤ) :
    start v = (![2, 5, 1], ![-2 * liftTriple v 0 + 2 * liftTriple v 1 + 2 * liftTriple v 2,
      -8 * liftTriple v 0 + 3 * liftTriple v 1 + 10 * liftTriple v 2, liftTriple v 2]) := by
  rw [start, first_eq]
  ext i <;> fin_cases i <;>
    norm_num [shadowMarkoffMutate, Function.update, Finset.sum_erase_eq_sub,
      Fin.sum_univ_three]
  ring

private lemma coord_fst (σ : ℚ) (s : State) (i : Fin 3) : (coord σ s i).fst = 3 * s.1 i := rfl

private lemma coord_snd (σ : ℚ) (s : State) (i : Fin 3) :
    (coord σ s i).snd = 3 * s.2 i + -σ * s.1 i := rfl

private lemma start_markoff (v : Fin 3 → ℤ) : Markoff (coord (weight v) (start v)) := by
  rw [markoff_iff (show Distinct 0 1 2 by unfold Distinct; decide), start_eq]
  apply TrivSqZeroExt.ext <;>
    simp only [pow_two, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.fst_mul, DualNumber.snd_mul, coord_snd, coord_fst, weight] <;>
    simp <;> ring

private def Region (p : Fin 3 → ℚ) : Prop :=
  0 ≤ p 0 ∧ 0 ≤ p 1 ∧ 0 ≤ p 2 ∧ 2 * p 0 ≤ p 1 + p 2 ∧ p 0 + p 1 ≤ 2 * p 2

-- At a lower node the last coordinate dominates both others in both parts
-- of the rescaled triple. These inequalities propagate under either forward mutation.
private def Dominates (f : Fin 3 → DualNumber ℚ) (l : Fin 3) : Prop :=
  ∀ i, (3 ≤ (f i).fst ∧ (f i).fst ≤ (f l).fst) ∧
    (0 ≤ (f i).snd ∧ (f i).snd ≤ (f l).snd)

private lemma dominates_mutate {σ : ℚ} {s : State} {i j l : Fin 3} (h : Distinct i j l)
    (hm : Markoff (coord σ s)) (hd : Dominates (coord σ s) l) :
    Dominates (coord σ (shadowMarkoffMutate i s)) i := by
  let f := coord σ s
  have hi := hd i
  have hj := hd j
  have hl := hd l
  change (3 ≤ (f i).fst ∧ _) ∧ (0 ≤ (f i).snd ∧ _) at hi
  change (3 ≤ (f j).fst ∧ _) ∧ (0 ≤ (f j).snd ∧ _) at hj
  have hfirst : (f l).fst ≤ (f j * f l - f i).fst := by
    simp only [TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul]
    nlinarith [mul_nonneg (show 0 ≤ (f j).fst - 2 by linarith [hj.1.1])
      (show 0 ≤ (f l).fst by linarith [hl.1.1])]
  have hsecond : (f l).snd ≤ (f j * f l - f i).snd := by
    simp only [TrivSqZeroExt.snd_sub, DualNumber.snd_mul]
    nlinarith [mul_nonneg (show 0 ≤ (f j).fst - 2 by linarith [hj.1.1]) hl.2.1,
      mul_nonneg hj.2.1 (show 0 ≤ (f l).fst by linarith [hl.1.1])]
  intro t
  rw [mutate_formula h hm (by linarith [hi.1.1])]
  by_cases ht : t = i
  · subst t
    rw [mutate_formula h hm (by linarith [hi.1.1])]
    exact ⟨⟨hl.1.1.trans hfirst, le_rfl⟩, hl.2.1.trans hsecond, le_rfl⟩
  · rw [coord_mutate_ne ht]
    exact ⟨⟨(hd t).1.1, (hd t).1.2.trans hfirst⟩, (hd t).2.1, (hd t).2.2.trans hsecond⟩

private lemma nonneg_of_region {v : Fin 3 → ℤ} (h : Region (liftTriple v)) :
    ∀ s ∈ shadowMarkoffTree v, 0 ≤ s.1 ∧ 0 ≤ s.2 := by
  obtain ⟨ha, hb, hc, hab, hbc⟩ := h
  have hσ : 0 ≤ weight v := by unfold weight; linarith
  intro s hs
  rcases hs with (rfl | rfl) | ⟨l, node⟩
  · exact ⟨fun _ => zero_le_one, fun i => by
      change 0 ≤ liftTriple v i
      fin_cases i <;> assumption⟩
  · rw [show shadowMarkoffMutate 0 (shadowMarkoffRoot v) = _ from first_eq v]
    constructor <;> intro i <;> fin_cases i <;> simp <;> linarith
  · have inv : Markoff (coord (weight v) s) ∧ Dominates (coord (weight v) s) l := by
      induction node with
      | start =>
        refine ⟨start_markoff v, ?_⟩
        intro i
        simp only [coord_fst, coord_snd, show shadowMarkoffMutate 1 (first v) = _ from
          start_eq v, weight]
        fin_cases i <;> norm_num <;> (repeat' constructor) <;> linarith
      | mutate i _ hne ih =>
        obtain ⟨j, hj⟩ := third_index hne
        exact ⟨markoff_mutate hj ih.1 (by linarith [(ih.2 i).1.1]),
          dominates_mutate hj ih.1 ih.2⟩
    have hx (i : Fin 3) : 0 ≤ s.1 i := by linarith [coord_fst (weight v) s i, (inv.2 i).1.1]
    refine ⟨hx, fun i => ?_⟩
    change 0 ≤ s.2 i
    linarith [coord_snd (weight v) s i, (inv.2 i).2.1, mul_nonneg hσ (hx i)]

-- Following alternating mutations leaves one dual coordinate b fixed.
private structure RayPoint (v : Fin 3 → ℤ) (b : DualNumber ℚ) where
  state : State
  prev : Fin 3
  fixed : Fin 3
  last : Fin 3
  indices : Distinct prev fixed last
  node : ShadowMarkoffTreeNode v state last
  equation : Markoff (coord (weight v) state)
  anchor : coord (weight v) state fixed = b
  lower : 3 ≤ (coord (weight v) state prev).fst
  increasing : (coord (weight v) state prev).fst ≤ (coord (weight v) state last).fst

private abbrev older {v b} (p : RayPoint v b) := coord (weight v) p.state p.prev

private abbrev newer {v b} (p : RayPoint v b) := coord (weight v) p.state p.last

private def advance {v b} (hb : 3 ≤ b.fst) (p : RayPoint v b) : RayPoint v b where
  state := shadowMarkoffMutate p.prev p.state
  prev := p.last
  fixed := p.fixed
  last := p.prev
  indices := ⟨p.indices.2.2.symm, p.indices.2.1.symm, p.indices.1.symm⟩
  node := .mutate _ p.node p.indices.2.1
  equation := markoff_mutate p.indices p.equation (by linarith [p.lower])
  anchor := (coord_mutate_ne p.indices.1.symm).trans p.anchor
  lower := by rw [coord_mutate_ne p.indices.2.1.symm]; exact p.lower.trans p.increasing
  increasing := by
    rw [coord_mutate_ne p.indices.2.1.symm,
      mutate_formula p.indices p.equation (by linarith [p.lower]), p.anchor]
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_sub]
    nlinarith [p.increasing, mul_nonneg (show 0 ≤ b.fst - 2 by linarith)
      (show 0 ≤ (newer p).fst by linarith [p.lower, p.increasing])]

private lemma older_advance {v b} (hb : 3 ≤ b.fst) (p : RayPoint v b) :
    older (advance hb p) = newer p := coord_mutate_ne p.indices.2.1.symm

private lemma newer_advance {v b} (hb : 3 ≤ b.fst) (p : RayPoint v b) :
    newer (advance hb p) = b * newer p - older p := by
  change coord _ (shadowMarkoffMutate _ _) p.prev = _
  rw [mutate_formula p.indices p.equation (by linarith [p.lower]), p.anchor]

-- The determinant of two consecutive pairs changes by b.snd times a positive square.
private def det {v b} (p : RayPoint v b) : ℚ :=
  (newer p).snd * (older p).fst - (older p).snd * (newer p).fst

private lemma det_advance {v b} (hb : 3 ≤ b.fst) (p : RayPoint v b) :
    det (advance hb p) = det p + b.snd * (newer p).fst ^ 2 := by
  simp only [det, older_advance, newer_advance, TrivSqZeroExt.fst_sub,
    TrivSqZeroExt.snd_sub, TrivSqZeroExt.fst_mul, DualNumber.snd_mul]
  ring

private lemma descent {α : Type} (f : α → ℚ) {d : ℚ} (hd : 0 < d)
    (step : ∀ p, ∃ q, f q ≤ f p - d) (p : α) (bound : ℚ) : ∃ q, f q < bound := by
  have iter (n : ℕ) : ∃ q, f q ≤ f p - n * d := by
    induction n with
    | zero => exact ⟨p, by simp⟩
    | succ n ih =>
      obtain ⟨q, hq⟩ := ih
      obtain ⟨r, hr⟩ := step q
      exact ⟨r, by push_cast; linarith⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((f p - bound) / d)
  obtain ⟨q, hq⟩ := iter n
  exact ⟨q, by linarith [(div_lt_iff₀ hd).mp hn]⟩

private lemma anchor_nonneg {v b} (hb : 3 ≤ b.fst) (initial : RayPoint v b)
    (hall : ∀ s ∈ shadowMarkoffTree v, 0 ≤ s.1 ∧ 0 ≤ s.2) : 0 ≤ b.snd := by
  by_contra! hneg
  -- First the determinant decreases by at least -b.snd per mutation.
  have hdet (p : RayPoint v b) : det (advance hb p) ≤ det p + b.snd := by
    rw [det_advance]
    have hc : 1 ≤ (newer p).fst := by linarith [p.lower, p.increasing]
    have hsq : 1 ≤ (newer p).fst ^ 2 := by nlinarith [sq_nonneg ((newer p).fst - 1)]
    linarith [mul_le_mul_of_nonpos_left hsq hneg.le]
  obtain ⟨p, hp⟩ := descent det (neg_pos.mpr hneg)
    (fun p => ⟨advance hb p, by simpa using hdet p⟩) initial 0
  let ratio (q : {p : RayPoint v b // det p ≤ 0}) := (newer q.val).snd / (newer q.val).fst
  -- Once the determinant is nonpositive, the ratio decreases by at least -b.snd / b.fst.
  have decrease (q : {p : RayPoint v b // det p ≤ 0}) :
      ∃ r, ratio r ≤ ratio q - (-b.snd / b.fst) := by
    let r := advance hb q.val
    have hr : det r ≤ 0 := by linarith [hdet q.val, q.property]
    refine ⟨⟨r, hr⟩, ?_⟩
    have hc : 0 < (newer q.val).fst := by linarith [q.val.lower, q.val.increasing]
    have hn : 0 < (newer r).fst := by linarith [r.lower, r.increasing]
    have hb' : 0 < b.fst := by linarith
    have hupper : (newer r).fst ≤ b.fst * (newer q.val).fst := by
      dsimp only [r]
      rw [newer_advance, TrivSqZeroExt.fst_sub, TrivSqZeroExt.fst_mul]
      linarith [q.val.lower]
    have hdiff : ratio ⟨r, hr⟩ - ratio q =
        det r / ((newer r).fst * (newer q.val).fst) := by
      dsimp only [ratio, det, r]
      rw [older_advance, div_sub_div _ _ hn.ne' hc.ne', mul_comm (newer r).fst (newer q.val).snd]
    have hnum : det r ≤ b.snd * (newer q.val).fst ^ 2 := by
      dsimp only [r]
      rw [det_advance]
      linarith [q.property]
    have hden := mul_le_mul_of_nonneg_right hupper hc.le
    have hbound : det r / ((newer r).fst * (newer q.val).fst) ≤ b.snd / b.fst := by
      apply (div_le_div_iff₀ (mul_pos hn hc) hb').mpr
      calc
        det r * b.fst ≤ (b.snd * (newer q.val).fst ^ 2) * b.fst :=
          mul_le_mul_of_nonneg_right hnum hb'.le
        _ = b.snd * (b.fst * (newer q.val).fst * (newer q.val).fst) := by ring
        _ ≤ _ := mul_le_mul_of_nonpos_left hden hneg.le
    simpa only [neg_div, sub_neg_eq_add, add_comm] using
      sub_le_iff_le_add.mp (hdiff.trans_le hbound)
  obtain ⟨q, hq⟩ := descent ratio (div_pos (neg_pos.mpr hneg) (by linarith)) decrease
    ⟨p, hp.le⟩ (-weight v / 3)
  have hx : 0 < (newer q.val).fst := by linarith [q.val.lower, q.val.increasing]
  have hy := (hall q.val.state (Or.inr ⟨_, q.val.node⟩)).2 q.val.last
  change 0 ≤ q.val.state.2 q.val.last at hy
  have hlt := (div_lt_iff₀ hx).mp hq
  rw [show newer q.val = coord _ _ _ from rfl, coord_snd, coord_fst] at hlt
  linarith

private lemma region_of_nonneg {v : Fin 3 → ℤ}
    (hall : ∀ s ∈ shadowMarkoffTree v, 0 ≤ s.1 ∧ 0 ≤ s.2) : Region (liftTriple v) := by
  have root := (hall (shadowMarkoffRoot v) (Or.inl (Or.inl rfl))).2
  let f := coord (weight v) (start v)
  have fixed_nonneg (i j : Fin 3) (h : Distinct i j 1) (hb : 3 ≤ (f j).fst)
      (ha : 3 ≤ (f i).fst) (hc : (f i).fst ≤ (f 1).fst) : 0 ≤ (f j).snd :=
    anchor_nonneg hb ⟨start v, i, j, 1, h, .start, start_markoff v, rfl, ha, hc⟩ hall
  have firstBound := fixed_nonneg 2 0 (by unfold Distinct; decide)
  have secondBound := fixed_nonneg 0 2 (by unfold Distinct; decide)
  norm_num [f, start_eq, coord_fst, coord_snd, weight] at firstBound secondBound
  exact ⟨root 0, root 1, root 2, by linarith, by linarith⟩

private def vertex : Fin 4 → Fin 3 → ℚ :=
  ![![0, 0, 3], ![0, 2, 1], ![1, 0, 2], ![1, 1, 1]]

private def vertices : Finset (Fin 3 → ℚ) := Finset.univ.image vertex

private lemma mem_vertices (i : Fin 4) : vertex i ∈ vertices :=
  Finset.mem_image_of_mem _ (Finset.mem_univ i)

private lemma region_smul {p : Fin 3 → ℚ} (hp : Region p) {t : ℚ} (ht : 0 ≤ t) :
    Region (t • p) := by
  obtain ⟨h₀, h₁, h₂, ha, hc⟩ := hp
  refine ⟨mul_nonneg ht h₀, mul_nonneg ht h₁, mul_nonneg ht h₂, ?_, ?_⟩
  · simpa [mul_add, mul_left_comm] using mul_le_mul_of_nonneg_left ha ht
  · simpa [mul_add, mul_left_comm] using mul_le_mul_of_nonneg_left hc ht

private lemma hull_region : convexHull ℚ (vertices : Set (Fin 3 → ℚ)) ⊆ {p | Region p} := by
  apply convexHull_min
  · intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    change Region (vertex i)
    fin_cases i <;> norm_num [vertex, Region]
  · intro p hp q hq a b ha hb _
    obtain ⟨p₀, p₁, p₂, pa, pc⟩ := region_smul hp ha
    obtain ⟨q₀, q₁, q₂, qa, qc⟩ := region_smul hq hb
    exact ⟨add_nonneg p₀ q₀, add_nonneg p₁ q₁, add_nonneg p₂ q₂,
      by dsimp only [Pi.add_apply]; linarith, by dsimp only [Pi.add_apply]; linarith⟩

private lemma cone_of_region {p : Fin 3 → ℚ} (hp : Region p) :
    ∃ t : ℚ, 0 ≤ t ∧ ∃ z ∈ convexHull ℚ (vertices : Set (Fin 3 → ℚ)), p = t • z := by
  obtain ⟨ha, hb, hc, hab, hbc⟩ := hp
  let m := min (p 0) (p 1)
  let w : Fin 4 → ℚ :=
    ![(p 2 - 2 * p 0 - p 1 / 2 + 3 * m / 2) / 3, (p 1 - m) / 2, p 0 - m, m]
  have hw (i) : 0 ≤ w i := by
    fin_cases i <;> simp [w, m, min_def] <;> split <;> linarith
  have hsum : ∑ i, w i • vertex i = p := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_succ, w, vertex]
    ring
  have ht : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => hw i
  rcases ht.eq_or_lt with ht | ht
  · have hz (i) : w i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hw j).mp ht.symm i (Finset.mem_univ i)
    exact ⟨0, le_rfl, vertex 0, subset_convexHull _ _ (mem_vertices 0), by
      simpa [hz] using hsum.symm⟩
  · refine ⟨_, ht.le, _, Finset.univ.centerMass_mem_convexHull (fun i _ => hw i) ht
      (fun i _ => mem_vertices i), ?_⟩
    simp [Finset.centerMass, smul_smul, ht.ne', hsum]

end ShadowMarkoffPolygon

open ShadowMarkoffPolygon

/-- **Nonnegativity on a shadow Markoff tree is governed by finitely many points.** There is a
finite set $V \subseteq \mathbb{Q}^3$ such that for every
$v = (\alpha, \beta, \gamma) \in \mathbb{Z}^3$ the following are equivalent: every state $(x, y)$
of the shadow Markoff tree of $v$, the tree of the initial triple
$(1 + \alpha\varepsilon, 1 + \beta\varepsilon, 1 + \gamma\varepsilon)$ with $\varepsilon^2 = 0$,
has all coordinates of its classical part $x$ and of its shadow part $y$ nonnegative; and $v = tw$
for some rational $t \ge 0$ and some point $w$ of the convex hull of $V$ in $\mathbb{Q}^3$.

In projective terms, the source describes the points $(\alpha : \beta : \gamma)$ with a
nonnegative tree as a convex polygon in an affine chart of the rational projective plane; the
statement above asserts only that some finite set $V$ exists.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Theorem 2 (`jis-2024-24.8.3-thm-2`). -/
public theorem exists_polygon_shadowMarkoffTree_nonneg_iff :
    ∃ V : Finset (Fin 3 → ℚ), ∀ v : Fin 3 → ℤ,
      (∀ s ∈ shadowMarkoffTree v, 0 ≤ s.1 ∧ 0 ≤ s.2) ↔
        ∃ t : ℚ, 0 ≤ t ∧ ∃ p ∈ convexHull ℚ (V : Set (Fin 3 → ℚ)),
          (fun i => (v i : ℚ)) = t • p := by
  refine ⟨vertices, fun v => ⟨fun h => cone_of_region (region_of_nonneg h), ?_⟩⟩
  rintro ⟨t, ht, p, hp, heq⟩
  apply nonneg_of_region
  change Region (fun i => (v i : ℚ))
  rw [heq]
  exact region_smul (hull_region hp) ht

end MetaMathlibExt
