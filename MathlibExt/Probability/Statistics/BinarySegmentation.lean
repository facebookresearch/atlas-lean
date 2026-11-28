/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Order.SymmDiff
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Binary segmentation selects a polyhedral cone of data vectors

For data `y ∈ ℝⁿ` and positions `1 ≤ s ≤ b < e ≤ n` (numbered from `1`, as in the source), the
CUSUM statistic of the split of the segment `{s, …, e}` after `b` is
`g_{(s,b,e)}ᵀ y = √(1 / (1 / (e - b) + 1 / (b + 1 - s))) (ȳ_{(b+1):e} - ȳ_{s:b})`, where `ȳ_{a:c}`
is the mean of `y_a, …, y_c`. The `k`-step binary segmentation algorithm, at each step
`ℓ = 1, …, k`, splits the partition of `{1, …, n}` induced by the changepoints `b̂_1, …, b̂_{ℓ-1}`
found so far at the split point of largest `|g_{(s,b,e)}ᵀ y|`, where `{s, …, e}` is the segment
of that partition containing `b` and `b + 1`, and records the location `b̂_ℓ` and the direction
`d̂_ℓ = sign(g_{(s,b̂_ℓ,e)}ᵀ y)`, with a fixed rule for ties and a fixed value of `sign 0`.

For feasible locations `b_{1:k}` (distinct elements of `{1, …, n - 1}`) and directions
`d_{1:k}`, the event that binary segmentation selects them lies between the open and the closed
convex polyhedral cones `{y : Γ y > 0}` and `{y : Γ y ≥ 0}` of an explicit matrix `Γ`, whatever
the tie-breaking rule. So it agrees with the closed cone outside the hyperplanes of the rows of
`Γ`, that is almost everywhere, though it need not equal it. Step `ℓ` contributes the sign row
`d_ℓ g_ℓ` and, for every competing split point `c`, the two rows `d_ℓ g_ℓ ∓ g_c`, where `g_ℓ` and
`g_c` are the CUSUM contrasts of `b_ℓ` and `c` in their segments. This corrects the statement of
Hyun, Lin, G'Sell and Tibshirani (2021, Proposition 1), as the implementation notes explain.

## Main definitions

* `cusum y s b e`: the CUSUM statistic `g_{(s,b,e)}ᵀ y`, and `cusumContrast n s b e` the vector
  `g_{(s,b,e)}`, with `cusumContrast n s b e ⬝ᵥ y = cusum y s b e`.
* `segmentStart B b`, `segmentEnd n B b`: the segment of the partition induced by the
  changepoints `B` that has `b` as a split point.
* `TieBreak`: a rule for breaking ties in the argmax.
* `model rule sign0 y k`: the ordered history `M^{BS}_{1:k}(y)` of the locations and directions
  that `k` steps of binary segmentation select (a run stops once no split point is free), and
  `selectionEvent n rule sign0 b d` the set of data vectors for which it is `{b_{1:k}, d_{1:k}}`.
* `selectionRow n b d`: the rows of the matrix `Γ`.

## Main results

* `exists_polyhedral_selectionEvent`: for feasible locations `b_{1:k}` (distinct elements of
  `{1, …, n - 1}`) and any directions `d_{1:k} ∈ {-1, +1}ᵏ`, there is a matrix `Γ` with
  `∑_{ℓ=1}^{k} (2 (n - ℓ - 1) + 1)` rows, none of them zero, such that
  `{y : Γ y > 0} ⊆ {y : M^{BS}_{1:k}(y) = {b_{1:k}, d_{1:k}}} ⊆ {y : Γ y ≥ 0}` for every
  tie-breaking rule and every value of `sign 0`; in particular the selection event agrees with
  the cone `{y : Γ y ≥ 0}` almost everywhere (their symmetric difference is Lebesgue-null),
  though not necessarily exactly.

## Implementation notes

The candidate pairs `(j, b)` of a step, an interval `I_j = {s_j, …, e_j}` of the current partition
and a split point `b ∈ {s_j, …, e_j - 1}` of it, correspond one to one to the split points
`b ∈ {1, …, n - 1}` that are not changepoints yet: the interval is then the one containing `b`
and `b + 1`, which `segmentStart` and `segmentEnd` compute. So the algorithm chooses among those
split points, and intervals of length one, which have no split point, never compete. A
tie-breaking rule may depend on the history of the run, hence on the partition. The source runs
`k ≤ n - 1` steps, which are always possible; a step is taken only while a split point is free, so
for `k > n - 1` the run stops after `n - 1` steps and selects no `k` locations.

The source's Proposition 1 states that the selection event equals `{y : Γ y ≥ 0}` for a matrix
with `2 ∑_{ℓ=1}^{k} (n - ℓ - 1)` rows, the comparison rows only, and does not deal with ties.
Ties break that equality: on a tie the tie-breaking rule may pick another split point, or the
direction of a zero CUSUM statistic is the fixed value of `sign 0`, while `Γ y ≥ 0` still holds.
A step with no competitor (`n - ℓ = 1`) has no comparison rows, so without a sign row its
direction would be unconstrained. So, for feasible locations, this module proves the two-sided
inclusion `{y : Γ y > 0} ⊆ {y : M^{BS}_{1:k}(y) = {b_{1:k}, d_{1:k}}} ⊆ {y : Γ y ≥ 0}`, with one
sign row per step, which gives `∑_{ℓ=1}^{k} (2 (n - ℓ - 1) + 1)` rows.

Locations are natural numbers, positions are numbered from `1`, and position `i` of
`y : Fin n → ℝ` is the coordinate `y ⟨i - 1, _⟩`. Directions are units of `ℤ`, that is `±1`.

## References

* S. Hyun, K. Z. Lin, M. G'Sell and R. J. Tibshirani, *Post-selection inference for changepoint
  detection algorithms with application to copy number variation data*, Biometrics 77 (2021),
  1037–1049, Section 2.1.1 (Eq. 3) and Section 3.1.1 (Proposition 1).
-/

@[expose] public section

open Finset Matrix MeasureTheory

namespace MathlibExt.Probability.Statistics.BinarySegmentation

variable {n k : ℕ}

/-! ### The CUSUM statistic and its contrast vector -/

/-- The sample mean `ȳ_{a:c} = (c - a + 1)⁻¹ ∑_{i=a}^{c} y_i` of `y : Fin n → ℝ` over the
positions `a, …, c`, numbered from `1`: position `i` is the coordinate `y ⟨i - 1, _⟩`, so the sum
runs over the coordinates `j` with `a ≤ j + 1 ≤ c`. It is meant for `1 ≤ a ≤ c ≤ n`. -/
noncomputable def segmentMean (y : Fin n → ℝ) (a c : ℕ) : ℝ :=
  (∑ j ∈ univ.filter fun j : Fin n => a ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ c, y j) / ((c : ℝ) - a + 1)

/-- The CUSUM statistic
`g_{(s,b,e)}ᵀ y = √(1 / (1 / (e - b) + 1 / (b + 1 - s))) (ȳ_{(b+1):e} - ȳ_{s:b})` of the split
of the segment `{s, …, e}` after position `b`, where `ȳ` is `segmentMean`. It is meant for
`1 ≤ s ≤ b < e ≤ n`. -/
noncomputable def cusum (y : Fin n → ℝ) (s b e : ℕ) : ℝ :=
  √(1 / (1 / ((e : ℝ) - b) + 1 / ((b : ℝ) + 1 - s))) *
    (segmentMean y (b + 1) e - segmentMean y s b)

/-- The CUSUM contrast `g_{(s,b,e)} ∈ ℝⁿ`, the vector with `g_{(s,b,e)} ⬝ᵥ y = cusum y s b e`
(`cusumContrast_dotProduct`): its coordinate at position `i` (numbered from `1`) is
`√(1 / (1 / (e - b) + 1 / (b + 1 - s)))` times `1 / (e - b)` if `b < i ≤ e`, `-1 / (b + 1 - s)`
if `s ≤ i ≤ b`, and `0` otherwise. -/
noncomputable def cusumContrast (n s b e : ℕ) : Fin n → ℝ := fun j =>
  √(1 / (1 / ((e : ℝ) - b) + 1 / ((b : ℝ) + 1 - s))) *
    ((if b + 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ e then 1 / ((e : ℝ) - b) else 0) -
      if s ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ b then 1 / ((b : ℝ) + 1 - s) else 0)

theorem cusumContrast_dotProduct (n s b e : ℕ) (y : Fin n → ℝ) :
    cusumContrast n s b e ⬝ᵥ y = cusum y s b e := by
  have key : ∀ (p : Fin n → Prop) [DecidablePred p] (x : ℝ),
      ∑ j, (if p j then x else 0) * y j = x * ∑ j with p j, y j := by
    intro p _ x
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  simp only [dotProduct, cusumContrast, cusum, segmentMean, mul_assoc, ← Finset.mul_sum,
    sub_mul, Finset.sum_sub_distrib, key]
  push_cast
  ring

theorem cusum_coeff_pos {s b e : ℕ} (hsb : s ≤ b) (hbe : b < e) :
    0 < √(1 / (1 / ((e : ℝ) - b) + 1 / ((b : ℝ) + 1 - s))) := by
  have h1 : (0 : ℝ) < e - b := by
    have : (b : ℝ) < e := by exact_mod_cast hbe
    linarith
  have h2 : (0 : ℝ) < b + 1 - s := by
    have : (s : ℝ) ≤ b := by exact_mod_cast hsb
    linarith
  exact Real.sqrt_pos.2 (one_div_pos.2 (add_pos (one_div_pos.2 h1) (one_div_pos.2 h2)))

theorem cusumContrast_neg_iff {s b e : ℕ} (hsb : s ≤ b) (hbe : b < e) (j : Fin n) :
    cusumContrast n s b e j < 0 ↔ s ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ b := by
  have hc := cusum_coeff_pos hsb hbe
  have h1 : (0 : ℝ) < 1 / ((e : ℝ) - b) := by
    have : (b : ℝ) < e := by exact_mod_cast hbe
    exact one_div_pos.2 (by linarith)
  have h2 : (0 : ℝ) < 1 / ((b : ℝ) + 1 - s) := by
    have : (s : ℝ) ≤ b := by exact_mod_cast hsb
    exact one_div_pos.2 (by linarith)
  unfold cusumContrast
  by_cases hA : b + 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ e
  · have hB : ¬(s ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ b) := by omega
    rw [ite_eq_left hA, ite_eq_right hB, sub_zero]
    exact iff_of_false (not_lt.2 (mul_pos hc h1).le) hB
  · by_cases hB : s ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ b
    · rw [ite_eq_right hA, ite_eq_left hB, zero_sub, mul_neg]
      exact iff_of_true (neg_neg_of_pos (mul_pos hc h2)) hB
    · rw [ite_eq_right hA, ite_eq_right hB, sub_zero, mul_zero]
      exact iff_of_false (lt_irrefl 0) hB

theorem cusumContrast_pos_iff {s b e : ℕ} (hsb : s ≤ b) (hbe : b < e) (j : Fin n) :
    0 < cusumContrast n s b e j ↔ b + 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ e := by
  have hc := cusum_coeff_pos hsb hbe
  have h1 : (0 : ℝ) < 1 / ((e : ℝ) - b) := by
    have : (b : ℝ) < e := by exact_mod_cast hbe
    exact one_div_pos.2 (by linarith)
  have h2 : (0 : ℝ) < 1 / ((b : ℝ) + 1 - s) := by
    have : (s : ℝ) ≤ b := by exact_mod_cast hsb
    exact one_div_pos.2 (by linarith)
  unfold cusumContrast
  by_cases hA : b + 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ e
  · have hB : ¬(s ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ b) := by omega
    rw [ite_eq_left hA, ite_eq_right hB, sub_zero]
    exact iff_of_true (mul_pos hc h1) hA
  · by_cases hB : s ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ b
    · rw [ite_eq_right hA, ite_eq_left hB, zero_sub, mul_neg]
      exact iff_of_false (not_lt.2 (neg_nonpos.2 (mul_pos hc h2).le)) hA
    · rw [ite_eq_right hA, ite_eq_right hB, sub_zero, mul_zero]
      exact iff_of_false (lt_irrefl 0) hA

/- Contrasts of different split points are neither equal nor opposite:
`g_{(s',b',e')} ≠ ± g_{(s,b,e)}`. -/
theorem cusumContrast_ne_smul {s b e s' b' e' : ℕ} (hs : 1 ≤ s) (hsb : s ≤ b) (hbe : b < e)
    (hen : e ≤ n) (hs' : 1 ≤ s') (hsb' : s' ≤ b') (hbe' : b' < e') (hen' : e' ≤ n)
    (hbb' : b ≠ b') (u : ℤˣ) :
    cusumContrast n s' b' e' ≠ ((u : ℤ) : ℝ) • cusumContrast n s b e := by
  intro h
  have hb : b - 1 < n := by omega
  have hb' : b' - 1 < n := by omega
  have hi := congrFun h ⟨b - 1, hb⟩
  have hi' := congrFun h ⟨b' - 1, hb'⟩
  simp only [Pi.smul_apply, smul_eq_mul] at hi hi'
  have gneg : cusumContrast n s b e ⟨b - 1, hb⟩ < 0 :=
    (cusumContrast_neg_iff hsb hbe _).2 (by simp only; omega)
  have gneg' : cusumContrast n s' b' e' ⟨b' - 1, hb'⟩ < 0 :=
    (cusumContrast_neg_iff hsb' hbe' _).2 (by simp only; omega)
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [Units.val_one, Int.cast_one, one_mul] at hi hi'
    have h1 := (cusumContrast_neg_iff hsb' hbe' _).1 (hi ▸ gneg)
    have h2 := (cusumContrast_neg_iff hsb hbe _).1 (hi' ▸ gneg')
    simp only at h1 h2
    omega
  · simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
      at hi hi'
    have h1 := (cusumContrast_pos_iff hsb' hbe' _).1 (by rw [hi]; linarith)
    have h2 := (cusumContrast_pos_iff hsb hbe _).1 (by linarith)
    simp only at h1 h2
    omega

theorem cusumContrast_ne_zero {s b e : ℕ} (hs : 1 ≤ s) (hsb : s ≤ b) (hbe : b < e)
    (hen : e ≤ n) : cusumContrast n s b e ≠ 0 := by
  intro h
  have hb : b - 1 < n := by omega
  have := (cusumContrast_neg_iff (n := n) hsb hbe ⟨b - 1, hb⟩).2 (by simp only; omega)
  rw [h] at this
  exact lt_irrefl _ this

/-! ### Binary segmentation -/

/-- The first position `s` of the segment of the partition of `{1, …, n}` induced by the
changepoints `B` (a changepoint `c` ends a segment at `c`) that has `b` as a split point: one more
than the largest changepoint below `b`, or `1` if there is none. -/
def segmentStart (B : Finset ℕ) (b : ℕ) : ℕ :=
  (B.filter (· < b)).sup id + 1

/-- The last position `e` of the segment of the partition of `{1, …, n}` induced by the
changepoints `B` that has `b` as a split point: the smallest changepoint above `b`, or `n` if
there is none. -/
def segmentEnd (n : ℕ) (B : Finset ℕ) (b : ℕ) : ℕ :=
  (insert n (B.filter (b < ·))).min' (insert_nonempty _ _)

theorem one_le_segmentStart (B : Finset ℕ) (b : ℕ) : 1 ≤ segmentStart B b :=
  Nat.le_add_left 1 _

theorem segmentStart_le {B : Finset ℕ} {b : ℕ} (hb : 1 ≤ b) : segmentStart B b ≤ b := by
  have : (B.filter (· < b)).sup id ≤ b - 1 :=
    Finset.sup_le fun x hx => by
      simp only [mem_filter] at hx
      simp only [id]
      omega
  unfold segmentStart
  omega

theorem lt_segmentEnd {B : Finset ℕ} {b : ℕ} (hbn : b < n) : b < segmentEnd n B b := by
  unfold segmentEnd
  rw [Finset.lt_min'_iff]
  intro x hx
  simp only [mem_insert, mem_filter] at hx
  rcases hx with rfl | ⟨_, h⟩
  · exact hbn
  · exact h

theorem segmentEnd_le (B : Finset ℕ) (b : ℕ) : segmentEnd n B b ≤ n :=
  Finset.min'_le _ _ (mem_insert_self _ _)

/- For a split point `b` that is not a changepoint, `{segmentStart B b, …, segmentEnd n B b}` is a
segment of the partition induced by `B`: it starts after `0` or a changepoint, ends at `n` or a
changepoint, and holds no changepoint before its end. -/

theorem segmentStart_sub_one_eq_zero_or_mem (B : Finset ℕ) (b : ℕ) :
    segmentStart B b - 1 = 0 ∨ segmentStart B b - 1 ∈ B := by
  unfold segmentStart
  rw [Nat.add_sub_cancel]
  rcases (B.filter (· < b)).eq_empty_or_nonempty with h | h
  · left
    rw [h]
    rfl
  · right
    obtain ⟨x, hx, hsup⟩ := Finset.exists_mem_eq_sup _ h id
    rw [hsup]
    exact (mem_filter.1 hx).1

theorem segmentEnd_eq_or_mem (n : ℕ) (B : Finset ℕ) (b : ℕ) :
    segmentEnd n B b = n ∨ segmentEnd n B b ∈ B := by
  have := Finset.min'_mem (insert n (B.filter (b < ·))) (insert_nonempty _ _)
  rw [mem_insert, mem_filter] at this
  unfold segmentEnd
  tauto

theorem notMem_of_segmentStart_le_of_lt_segmentEnd {B : Finset ℕ} {b c : ℕ} (hbB : b ∉ B)
    (hs : segmentStart B b ≤ c) (he : c < segmentEnd n B b) : c ∉ B := by
  intro hc
  rcases lt_trichotomy c b with h | rfl | h
  · have : c ≤ (B.filter (· < b)).sup id := Finset.le_sup (f := id) (mem_filter.2 ⟨hc, h⟩)
    unfold segmentStart at hs
    omega
  · exact hbB hc
  · have : segmentEnd n B b ≤ c :=
      Finset.min'_le _ _ (mem_insert_of_mem (mem_filter.2 ⟨hc, h⟩))
    omega

/-- The split points `{1, …, n - 1} \ B` that are not changepoints once the changepoints `B` are
found: each is a split point of exactly one segment of the partition that `B` induces. -/
def freeSplits (n : ℕ) (B : Finset ℕ) : Finset ℕ :=
  Icc 1 (n - 1) \ B

/-- The CUSUM statistic `g_{(s,b,e)}ᵀ y` of the split after position `b` of its segment
`{s, …, e}` of the partition induced by the changepoints `B`. -/
noncomputable def splitCusum (y : Fin n → ℝ) (B : Finset ℕ) (b : ℕ) : ℝ :=
  cusum y (segmentStart B b) b (segmentEnd n B b)

/-- The argmax of one step of binary segmentation once the changepoints `B` are found: the
split points `b ∈ freeSplits n B` with the largest `|splitCusum y B b|`. -/
noncomputable def bestSplits (y : Fin n → ℝ) (B : Finset ℕ) : Finset ℕ :=
  (freeSplits n B).filter fun b => ∀ c ∈ freeSplits n B, |splitCusum y B c| ≤ |splitCusum y B b|

/-- A rule for breaking ties in the argmax of binary segmentation: from the history of the
locations and directions selected so far and the set of tied split points, it picks one of
them whenever there is one. -/
structure TieBreak where
  /-- The split point picked, from the history so far and the set of tied split points. -/
  pick : List (ℕ × ℤˣ) → Finset ℕ → ℕ
  /-- The picked split point is one of the tied ones, when there is one. -/
  pick_mem : ∀ H S, S.Nonempty → pick H S ∈ S

/-- The direction `sign t ∈ {-1, +1}`, as a unit of `ℤ`, with the convention `sign 0 = sign0`. -/
noncomputable def direction (sign0 : ℤˣ) (t : ℝ) : ℤˣ :=
  if 0 < t then 1 else if t < 0 then -1 else sign0

/-- One step of binary segmentation after the history `H` of locations and directions selected so
far, when a split point is still free: the location `b` that the tie-breaking rule picks among
the split points maximising `|g_{(s,b,e)}ᵀ y|` over the segments `{s, …, e}` of the partition
induced by the locations of `H`, and its direction `sign(g_{(s,b,e)}ᵀ y)`. When no split point is
free, `b` is whatever the rule returns on the empty set; `model` takes no step then. -/
noncomputable def step (rule : TieBreak) (sign0 : ℤˣ) (y : Fin n → ℝ) (H : List (ℕ × ℤˣ)) :
    ℕ × ℤˣ :=
  let B := (H.map Prod.fst).toFinset
  let b := rule.pick H (bestSplits y B)
  (b, direction sign0 (splitCusum y B b))

/-- The model `M^{BS}_{1:k}(y) = {b̂_{1:k}(y), d̂_{1:k}(y)}` that `k` steps of binary segmentation
select from the data `y`, with the tie-breaking rule `rule` and `sign 0 = sign0`: the ordered
history of the locations and directions, step `ℓ` being its `ℓ`-th entry. A step is taken only
while some split point is free, so the run stops after `n - 1` steps: for `k ≤ n - 1` the history
has `k` entries (`length_model_of_le`), and for larger `k` it has only `n - 1`, so it selects no
`k` locations. -/
noncomputable def model (rule : TieBreak) (sign0 : ℤˣ) (y : Fin n → ℝ) : ℕ → List (ℕ × ℤˣ)
  | 0 => []
  | k + 1 =>
    if (freeSplits n ((model rule sign0 y k).map Prod.fst).toFinset).Nonempty then
      model rule sign0 y k ++ [step rule sign0 y (model rule sign0 y k)]
    else model rule sign0 y k

/-- The selection event `{y ∈ ℝⁿ : M^{BS}_{1:k}(y) = {b_{1:k}, d_{1:k}}}` of the locations
`b_{1:k}` and directions `d_{1:k}` (step `ℓ + 1` is index `ℓ : Fin k`). -/
def selectionEvent (n : ℕ) (rule : TieBreak) (sign0 : ℤˣ) (b : Fin k → ℕ) (d : Fin k → ℤˣ) :
    Set (Fin n → ℝ) :=
  {y | model rule sign0 y k = List.ofFn fun ℓ => (b ℓ, d ℓ)}

theorem abs_eq_direction_mul (sign0 : ℤˣ) (t : ℝ) :
    |t| = ((direction sign0 t : ℤ) : ℝ) * t := by
  unfold direction
  split_ifs with h1 h2
  · simp [abs_of_pos h1]
  · simp [abs_of_neg h2]
  · have : t = 0 := by linarith [not_lt.1 h1, not_lt.1 h2]
    simp [this]

theorem direction_eq_of_pos_mul {sign0 u : ℤˣ} {t : ℝ} (h : 0 < ((u : ℤ) : ℝ) * t) :
    direction sign0 t = u := by
  unfold direction
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [Units.val_one, Int.cast_one, one_mul] at h
    simp [h]
  · simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul,
      Left.neg_pos_iff] at h
    simp [h, not_lt.2 h.le]

/- If a step selects `(b₀, d₀)` while some split point is free, then `b₀` maximises
`|splitCusum y B ·|` and `d₀ * splitCusum y B b₀ = |splitCusum y B b₀|`. -/
theorem step_spec {rule : TieBreak} {sign0 : ℤˣ} {y : Fin n → ℝ} {H : List (ℕ × ℤˣ)}
    {b₀ : ℕ} {d₀ : ℤˣ} (hstep : step rule sign0 y H = (b₀, d₀))
    (hne : (freeSplits n (H.map Prod.fst).toFinset).Nonempty) :
    b₀ ∈ bestSplits y (H.map Prod.fst).toFinset ∧
      |splitCusum y (H.map Prod.fst).toFinset b₀| =
        ((d₀ : ℤ) : ℝ) * splitCusum y (H.map Prod.fst).toFinset b₀ := by
  set B := (H.map Prod.fst).toFinset
  simp only [step, Prod.mk.injEq] at hstep
  obtain ⟨hb, hd⟩ := hstep
  have hbest : (bestSplits y B).Nonempty := by
    obtain ⟨c, hc, hmax⟩ := (freeSplits n B).exists_max_image (fun c => |splitCusum y B c|) hne
    exact ⟨c, mem_filter.2 ⟨hc, hmax⟩⟩
  have hmem := rule.pick_mem H _ hbest
  rw [hb] at hmem
  refine ⟨hmem, ?_⟩
  rw [← hd, ← hb]
  exact abs_eq_direction_mul _ _

/- A step selects `(b₀, d₀)` when `b₀` is a free split point, `d₀ * splitCusum y B b₀ > 0`, and
every other free split point `c` has `|splitCusum y B c| < d₀ * splitCusum y B b₀`. -/
theorem step_eq_of_lt {rule : TieBreak} {sign0 : ℤˣ} {y : Fin n → ℝ} {H : List (ℕ × ℤˣ)}
    {b₀ : ℕ} {d₀ : ℤˣ} (hb₀ : b₀ ∈ freeSplits n (H.map Prod.fst).toFinset)
    (hpos : 0 < ((d₀ : ℤ) : ℝ) * splitCusum y (H.map Prod.fst).toFinset b₀)
    (hlt : ∀ c ∈ freeSplits n (H.map Prod.fst).toFinset, c ≠ b₀ →
      |splitCusum y (H.map Prod.fst).toFinset c| <
        ((d₀ : ℤ) : ℝ) * splitCusum y (H.map Prod.fst).toFinset b₀) :
    step rule sign0 y H = (b₀, d₀) := by
  set B := (H.map Prod.fst).toFinset
  have habs : |splitCusum y B b₀| = ((d₀ : ℤ) : ℝ) * splitCusum y B b₀ := by
    rw [← abs_of_pos hpos, abs_mul]
    rcases Int.units_eq_one_or d₀ with h | h <;> simp [h]
  have hbest : bestSplits y B = {b₀} := by
    ext c
    simp only [bestSplits, mem_filter, mem_singleton]
    constructor
    · rintro ⟨hc, hmax⟩
      by_contra hcb
      have := hmax b₀ hb₀
      linarith [hlt c hc hcb]
    · intro hc
      rw [hc]
      refine ⟨hb₀, fun c hc => ?_⟩
      by_cases hcb : c = b₀
      · rw [hcb]
      · linarith [hlt c hc hcb]
  have hpick : rule.pick H (bestSplits y B) = b₀ := by
    rw [hbest]
    exact mem_singleton.1 (rule.pick_mem H {b₀} (singleton_nonempty _))
  simp only [step, Prod.mk.injEq]
  refine ⟨hpick, ?_⟩
  rw [hpick]
  exact direction_eq_of_pos_mul hpos

theorem model_prefix (rule : TieBreak) (sign0 : ℤˣ) (y : Fin n → ℝ) {ℓ k : ℕ} (h : ℓ ≤ k) :
    model rule sign0 y ℓ <+: model rule sign0 y k := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    refine ih.trans ?_
    rw [model]
    split_ifs
    · exact List.prefix_append _ _
    · exact List.prefix_refl _

/- The locations that binary segmentation selects are distinct elements of `{1, …, n - 1}`: a step
is taken only while a split point is free, and it picks one. -/
theorem model_feasible (rule : TieBreak) (sign0 : ℤˣ) (y : Fin n → ℝ) :
    ∀ ℓ, ((model rule sign0 y ℓ).map Prod.fst).Nodup ∧
      ∀ x ∈ (model rule sign0 y ℓ).map Prod.fst, x ∈ Icc 1 (n - 1)
  | 0 => by simp [model]
  | ℓ + 1 => by
    obtain ⟨hnd, hmem⟩ := model_feasible rule sign0 y ℓ
    rw [model]
    split_ifs with hfree
    · set H := model rule sign0 y ℓ
      set B := (H.map Prod.fst).toFinset
      have hbest : (bestSplits y B).Nonempty := by
        obtain ⟨c, hc, hmax⟩ :=
          (freeSplits n B).exists_max_image (fun c => |splitCusum y B c|) hfree
        exact ⟨c, mem_filter.2 ⟨hc, hmax⟩⟩
      have hpick := mem_sdiff.1 (mem_filter.1 (rule.pick_mem H _ hbest)).1
      have hfst : (step rule sign0 y H).1 = rule.pick H (bestSplits y B) := rfl
      simp only [List.map_append, List.map_cons, List.map_nil]
      refine ⟨List.nodup_append.2 ⟨hnd, List.nodup_singleton _, ?_⟩, fun x hx => ?_⟩
      · intro a ha c hc
        rw [List.mem_singleton] at hc
        rintro rfl
        exact hpick.2 (by rw [hc, hfst] at ha; exact List.mem_toFinset.2 ha)
      · rcases List.mem_append.1 hx with hx | hx
        · exact hmem x hx
        · rw [List.mem_singleton.1 hx, hfst]
          exact hpick.1
    · exact ⟨hnd, hmem⟩

private theorem freeSplits_model_nonempty {rule : TieBreak} {sign0 : ℤˣ} {y : Fin n → ℝ}
    {ℓ : ℕ} (hℓ : ℓ < n - 1) (hlen : (model rule sign0 y ℓ).length = ℓ) :
    (freeSplits n ((model rule sign0 y ℓ).map Prod.fst).toFinset).Nonempty := by
  obtain ⟨hnd, hmem⟩ := model_feasible rule sign0 y ℓ
  have hsub : ((model rule sign0 y ℓ).map Prod.fst).toFinset ⊆ Icc 1 (n - 1) :=
    fun x hx => hmem x (List.mem_toFinset.1 hx)
  rw [← Finset.card_pos, freeSplits, card_sdiff_of_subset hsub, Nat.card_Icc,
    List.toFinset_card_of_nodup hnd, List.length_map, hlen]
  omega

/- For `ℓ ≤ n - 1` every one of the first `ℓ` steps is taken. -/
theorem length_model_of_le (rule : TieBreak) (sign0 : ℤˣ) (y : Fin n → ℝ) :
    ∀ ℓ ≤ n - 1, (model rule sign0 y ℓ).length = ℓ
  | 0, _ => rfl
  | ℓ + 1, hℓ => by
    have ih := length_model_of_le rule sign0 y ℓ (by omega)
    rw [model, ite_eq_left (freeSplits_model_nonempty (by omega) ih), List.length_append, ih]
    rfl

theorem model_succ_of_lt (rule : TieBreak) (sign0 : ℤˣ) (y : Fin n → ℝ) {ℓ : ℕ}
    (hℓ : ℓ < n - 1) :
    model rule sign0 y (ℓ + 1) =
      model rule sign0 y ℓ ++ [step rule sign0 y (model rule sign0 y ℓ)] := by
  rw [model, ite_eq_left (freeSplits_model_nonempty hℓ (length_model_of_le rule sign0 y ℓ hℓ.le))]

/- After `n - 1` steps no split point is free, and the run stops. -/
theorem model_succ_of_le (rule : TieBreak) (sign0 : ℤˣ) (y : Fin n → ℝ) {ℓ : ℕ}
    (hℓ : n - 1 ≤ ℓ) : model rule sign0 y (ℓ + 1) = model rule sign0 y ℓ := by
  obtain ⟨hnd, hmem⟩ := model_feasible rule sign0 y ℓ
  have hsub : ((model rule sign0 y ℓ).map Prod.fst).toFinset ⊆ Icc 1 (n - 1) :=
    fun x hx => hmem x (List.mem_toFinset.1 hx)
  have hlen : n - 1 ≤ (model rule sign0 y ℓ).length := by
    have := (model_prefix rule sign0 y hℓ).length_le
    rwa [length_model_of_le rule sign0 y (n - 1) le_rfl] at this
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Nat.card_Icc, List.toFinset_card_of_nodup hnd, List.length_map]
    omega)
  rw [model, ite_eq_right]
  rw [freeSplits, heq, Finset.sdiff_self]
  exact Finset.not_nonempty_empty

theorem model_take (rule : TieBreak) (sign0 : ℤˣ) (y : Fin n → ℝ) {ℓ k : ℕ} (h : ℓ ≤ k)
    (hk : k ≤ n - 1) : (model rule sign0 y k).take ℓ = model rule sign0 y ℓ := by
  have := List.prefix_iff_eq_take.1 (model_prefix rule sign0 y h)
  rw [length_model_of_le rule sign0 y ℓ (h.trans hk)] at this
  exact this.symm

/- The selection event of infeasible locations is empty. -/
theorem selectionEvent_eq_empty (rule : TieBreak) (sign0 : ℤˣ) {b : Fin k → ℕ}
    (d : Fin k → ℤˣ) (hb : ¬(Function.Injective b ∧ ∀ ℓ, b ℓ ∈ Icc 1 (n - 1))) :
    selectionEvent n rule sign0 b d = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun y hy => hb ?_
  obtain ⟨hnd, hmem⟩ := model_feasible rule sign0 y k
  have hy : model rule sign0 y k = List.ofFn fun ℓ => (b ℓ, d ℓ) := hy
  rw [hy, List.map_ofFn] at hnd hmem
  exact ⟨List.nodup_ofFn.1 hnd, fun ℓ => hmem _ (List.mem_ofFn.2 ⟨ℓ, rfl⟩)⟩

/- Feasible locations number at most `n - 1`. -/
theorem le_sub_one_of_feasible {b : Fin k → ℕ} (hb : Function.Injective b)
    (hbn : ∀ ℓ, b ℓ ∈ Icc 1 (n - 1)) : k ≤ n - 1 := by
  have := Finset.card_le_card_of_injOn b (s := univ) (t := Icc 1 (n - 1))
    (by intro ℓ _; exact hbn ℓ) hb.injOn
  simpa using this

/-! ### The matrix `Γ` -/

/-- The changepoints `b 0, …, b (ℓ - 1)` found by the first `ℓ` steps, steps being indexed from
`0` (the step of index `ℓ` is step `ℓ + 1` of the algorithm). -/
def priorSplits (b : Fin k → ℕ) (ℓ : ℕ) : Finset ℕ :=
  ((List.ofFn b).take ℓ).toFinset

/-- The competitors of the location `b ℓ` at the step of index `ℓ`: the split points other than
`b ℓ` that are free after the changepoints `priorSplits b ℓ`. For feasible locations there are
`n - (ℓ + 1) - 1` of them (`card_competitors`). -/
def competitors (n : ℕ) (b : Fin k → ℕ) (ℓ : Fin k) : Finset ℕ :=
  (freeSplits n (priorSplits b ℓ)).erase (b ℓ)

/-- The CUSUM contrast `g_{(s,c,e)}` of the split point `c` in its segment `{s, …, e}` of the
partition induced by `priorSplits b ℓ`, the changepoints found before the step of index `ℓ`. -/
noncomputable def stepContrast (n : ℕ) (b : Fin k → ℕ) (ℓ : Fin k) (c : ℕ) : Fin n → ℝ :=
  cusumContrast n (segmentStart (priorSplits b ℓ) c) c (segmentEnd n (priorSplits b ℓ) c)

/-- The rows of the matrix `Γ` of the selection event of the locations `b` and directions `d`.
With `g_ℓ = stepContrast n b ℓ (b ℓ)` the winning contrast of the step of index `ℓ`, that step
contributes the sign row `d_ℓ g_ℓ` (index `⟨ℓ, none⟩`) and, for each competitor `c`, the two rows
`d_ℓ g_ℓ - g_c` and `d_ℓ g_ℓ + g_c` (indices `⟨ℓ, some (c, true)⟩` and `⟨ℓ, some (c, false)⟩`),
where `g_c = stepContrast n b ℓ c`: the rows of `d_ℓ g_ℓᵀ y ≥ 0` and
`d_ℓ g_ℓᵀ y ≥ |g_cᵀ y|`. -/
noncomputable def selectionRow (n : ℕ) (b : Fin k → ℕ) (d : Fin k → ℤˣ) :
    (Σ ℓ : Fin k, Option (competitors n b ℓ × Bool)) → Fin n → ℝ
  | ⟨ℓ, none⟩ => ((d ℓ : ℤ) : ℝ) • stepContrast n b ℓ (b ℓ)
  | ⟨ℓ, some (c, true)⟩ => ((d ℓ : ℤ) : ℝ) • stepContrast n b ℓ (b ℓ) - stepContrast n b ℓ c
  | ⟨ℓ, some (c, false)⟩ => ((d ℓ : ℤ) : ℝ) • stepContrast n b ℓ (b ℓ) + stepContrast n b ℓ c

theorem mem_priorSplits {b : Fin k → ℕ} {ℓ x : ℕ} :
    x ∈ priorSplits b ℓ ↔ ∃ j : Fin k, (j : ℕ) < ℓ ∧ b j = x := by
  simp only [priorSplits, List.mem_toFinset, List.mem_take_iff_getElem, List.length_ofFn,
    List.getElem_ofFn]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨i, by omega⟩, ?_, rfl⟩
    change i < ℓ
    omega
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by omega, rfl⟩

theorem mem_freeSplits_priorSplits {b : Fin k → ℕ} (hb : Function.Injective b)
    (hbn : ∀ ℓ, b ℓ ∈ Icc 1 (n - 1)) (ℓ : Fin k) : b ℓ ∈ freeSplits n (priorSplits b ℓ) := by
  refine mem_sdiff.2 ⟨hbn ℓ, fun h => ?_⟩
  obtain ⟨j, hj, hbj⟩ := mem_priorSplits.1 h
  exact (Fin.ne_of_lt hj) (hb hbj)

theorem stepContrast_dotProduct (b : Fin k → ℕ) (ℓ : Fin k) (c : ℕ) (y : Fin n → ℝ) :
    stepContrast n b ℓ c ⬝ᵥ y = splitCusum y (priorSplits b ℓ) c :=
  cusumContrast_dotProduct _ _ _ _ y

private theorem segment_bounds {B : Finset ℕ} {c : ℕ} (hc : c ∈ freeSplits n B) :
    1 ≤ segmentStart B c ∧ segmentStart B c ≤ c ∧ c < segmentEnd n B c ∧
      segmentEnd n B c ≤ n := by
  have hc' := (mem_Icc.1 (mem_sdiff.1 hc).1)
  exact ⟨one_le_segmentStart B c, segmentStart_le hc'.1, lt_segmentEnd (by omega),
    segmentEnd_le B c⟩

theorem selectionRow_ne_zero {b : Fin k → ℕ} (hb : Function.Injective b)
    (hbn : ∀ ℓ, b ℓ ∈ Icc 1 (n - 1)) (d : Fin k → ℤˣ) (r) : selectionRow n b d r ≠ 0 := by
  obtain ⟨ℓ, r⟩ := r
  have hbℓ := segment_bounds (mem_freeSplits_priorSplits hb hbn ℓ)
  have hg : stepContrast n b ℓ (b ℓ) ≠ 0 :=
    cusumContrast_ne_zero hbℓ.1 hbℓ.2.1 hbℓ.2.2.1 hbℓ.2.2.2
  have hcomp : ∀ c ∈ competitors n b ℓ, ∀ u : ℤˣ,
      stepContrast n b ℓ c ≠ ((u : ℤ) : ℝ) • stepContrast n b ℓ (b ℓ) := by
    intro c hc u
    obtain ⟨hcb, hc⟩ := mem_erase.1 hc
    have hcℓ := segment_bounds hc
    exact cusumContrast_ne_smul hbℓ.1 hbℓ.2.1 hbℓ.2.2.1 hbℓ.2.2.2 hcℓ.1 hcℓ.2.1 hcℓ.2.2.1
      hcℓ.2.2.2 (Ne.symm hcb) u
  rcases r with _ | ⟨⟨c, hc⟩, _ | _⟩
  · simp only [selectionRow]
    rw [Ne, smul_eq_zero, not_or]
    exact ⟨by rcases Int.units_eq_one_or (d ℓ) with h | h <;> simp [h], hg⟩
  · simp only [selectionRow, Ne, add_eq_zero_iff_eq_neg]
    intro h
    refine hcomp c hc (-(d ℓ)) ?_
    rw [eq_neg_iff_add_eq_zero] at h
    rw [Units.val_neg, Int.cast_neg, neg_smul, eq_neg_iff_add_eq_zero, add_comm, h]
  · simp only [selectionRow, Ne, sub_eq_zero]
    exact fun h => hcomp c hc (d ℓ) h.symm

private theorem take_ofFn_succ (b : Fin k → ℕ) (d : Fin k → ℤˣ) (ℓ : Fin k) :
    (List.ofFn fun j => (b j, d j)).take (ℓ + 1) =
      (List.ofFn fun j => (b j, d j)).take ℓ ++ [(b ℓ, d ℓ)] := by
  rw [List.take_add_one, List.getElem?_ofFn]
  simp

private theorem map_fst_take_ofFn (b : Fin k → ℕ) (d : Fin k → ℤˣ) (ℓ : ℕ) :
    ((List.ofFn fun j => (b j, d j)).take ℓ).map Prod.fst = (List.ofFn b).take ℓ := by
  rw [List.map_take, List.map_ofFn]
  rfl

/- Upper inclusion: on the selection event every row of `Γ` is nonnegative. -/
theorem selectionRow_dotProduct_nonneg {b : Fin k → ℕ} (hb : Function.Injective b)
    (hbn : ∀ ℓ, b ℓ ∈ Icc 1 (n - 1)) (d : Fin k → ℤˣ) {rule : TieBreak} {sign0 : ℤˣ}
    {y : Fin n → ℝ} (hy : y ∈ selectionEvent n rule sign0 b d) (r) :
    0 ≤ selectionRow n b d r ⬝ᵥ y := by
  obtain ⟨ℓ, r⟩ := r
  set T := List.ofFn fun j => (b j, d j)
  have hy : model rule sign0 y k = T := hy
  have hk := le_sub_one_of_feasible hb hbn
  have hℓ : model rule sign0 y ℓ = T.take ℓ := by
    rw [← model_take rule sign0 y ℓ.2.le hk, hy]
  have hℓ1 : model rule sign0 y (ℓ + 1) = T.take (ℓ + 1) := by
    rw [← model_take rule sign0 y (Nat.succ_le_of_lt ℓ.2) hk, hy]
  have hstep : step rule sign0 y (T.take ℓ) = (b ℓ, d ℓ) := by
    rw [model_succ_of_lt rule sign0 y (lt_of_lt_of_le ℓ.2 hk), hℓ, take_ofFn_succ] at hℓ1
    simpa using List.append_cancel_left hℓ1
  have hB : ((T.take ℓ).map Prod.fst).toFinset = priorSplits b ℓ := by
    rw [map_fst_take_ofFn]; rfl
  have hfree := mem_freeSplits_priorSplits hb hbn ℓ
  obtain ⟨hbest, habs⟩ := step_spec hstep (by rw [hB]; exact ⟨_, hfree⟩)
  rw [hB] at hbest habs
  have hmax : ∀ c ∈ freeSplits n (priorSplits b ℓ),
      |splitCusum y (priorSplits b ℓ) c| ≤ |splitCusum y (priorSplits b ℓ) (b ℓ)| :=
    (mem_filter.1 hbest).2
  rcases r with _ | ⟨⟨c, hc⟩, _ | _⟩
  · simp only [selectionRow, smul_dotProduct, smul_eq_mul, stepContrast_dotProduct, ← habs]
    exact abs_nonneg _
  · simp only [selectionRow, add_dotProduct, smul_dotProduct, smul_eq_mul,
      stepContrast_dotProduct, ← habs]
    have := hmax c (mem_of_mem_erase hc)
    linarith [neg_abs_le (splitCusum y (priorSplits b ℓ) c)]
  · simp only [selectionRow, sub_dotProduct, smul_dotProduct, smul_eq_mul,
      stepContrast_dotProduct, ← habs]
    have := hmax c (mem_of_mem_erase hc)
    linarith [le_abs_self (splitCusum y (priorSplits b ℓ) c)]

/- Lower inclusion: where every row of `Γ` is positive, binary segmentation selects `b` and `d`,
whatever the tie-breaking rule and the value of `sign 0`. -/
theorem mem_selectionEvent_of_pos {b : Fin k → ℕ} (hb : Function.Injective b)
    (hbn : ∀ ℓ, b ℓ ∈ Icc 1 (n - 1)) (d : Fin k → ℤˣ) (rule : TieBreak) (sign0 : ℤˣ)
    {y : Fin n → ℝ} (hy : ∀ r, 0 < selectionRow n b d r ⬝ᵥ y) :
    y ∈ selectionEvent n rule sign0 b d := by
  set T := List.ofFn fun j => (b j, d j)
  have hk := le_sub_one_of_feasible hb hbn
  suffices h : ∀ ℓ ≤ k, model rule sign0 y ℓ = T.take ℓ by
    change model rule sign0 y k = T
    rw [h k le_rfl, List.take_of_length_le (by simp [T])]
  intro ℓ
  induction ℓ with
  | zero => intro _; rfl
  | succ ℓ ih =>
    intro hℓk
    have hℓ : ℓ < k := hℓk
    rw [model_succ_of_lt rule sign0 y (lt_of_lt_of_le hℓ hk), ih hℓ.le,
      show ℓ = ((⟨ℓ, hℓ⟩ : Fin k) : ℕ) from rfl, take_ofFn_succ]
    congr 2
    have hB : ((T.take ℓ).map Prod.fst).toFinset = priorSplits b ℓ := by
      rw [map_fst_take_ofFn]; rfl
    have hsign := hy ⟨⟨ℓ, hℓ⟩, none⟩
    simp only [selectionRow, smul_dotProduct, smul_eq_mul, stepContrast_dotProduct] at hsign
    refine step_eq_of_lt ?_ ?_ ?_ <;> rw [hB]
    · exact mem_freeSplits_priorSplits hb hbn ⟨ℓ, hℓ⟩
    · exact hsign
    · intro c hc hcb
      have hcomp : c ∈ competitors n b ⟨ℓ, hℓ⟩ := mem_erase.2 ⟨hcb, hc⟩
      have h1 := hy ⟨⟨ℓ, hℓ⟩, some (⟨c, hcomp⟩, true)⟩
      have h2 := hy ⟨⟨ℓ, hℓ⟩, some (⟨c, hcomp⟩, false)⟩
      simp only [selectionRow, add_dotProduct, sub_dotProduct, smul_dotProduct, smul_eq_mul,
        stepContrast_dotProduct] at h1 h2
      exact abs_lt.2 ⟨by linarith, by linarith⟩

theorem card_priorSplits {b : Fin k → ℕ} (hb : Function.Injective b) {ℓ : ℕ} (hℓ : ℓ ≤ k) :
    (priorSplits b ℓ).card = ℓ := by
  unfold priorSplits
  rw [List.toFinset_card_of_nodup ((List.nodup_ofFn.2 hb).sublist (List.take_sublist _ _)),
    List.length_take, List.length_ofFn, min_eq_left hℓ]

theorem card_competitors {b : Fin k → ℕ} (hb : Function.Injective b)
    (hbn : ∀ ℓ, b ℓ ∈ Icc 1 (n - 1)) (ℓ : Fin k) :
    (competitors n b ℓ).card = n - (ℓ + 1) - 1 := by
  have hsub : priorSplits b ℓ ⊆ Icc 1 (n - 1) := fun x hx => by
    obtain ⟨j, -, rfl⟩ := mem_priorSplits.1 hx
    exact hbn j
  unfold competitors
  rw [card_erase_of_mem (mem_freeSplits_priorSplits hb hbn ℓ)]
  unfold freeSplits
  rw [card_sdiff_of_subset hsub,
    card_priorSplits hb ℓ.2.le, Nat.card_Icc]
  omega

theorem card_selectionRow_index {b : Fin k → ℕ} (hb : Function.Injective b)
    (hbn : ∀ ℓ, b ℓ ∈ Icc 1 (n - 1)) :
    Fintype.card (Σ ℓ : Fin k, Option (competitors n b ℓ × Bool)) =
      ∑ ℓ ∈ Icc 1 k, (2 * (n - ℓ - 1) + 1) := by
  simp only [Fintype.card_sigma, Fintype.card_option, Fintype.card_prod, Fintype.card_coe,
    Fintype.card_bool, card_competitors hb hbn]
  rw [Fin.sum_univ_eq_sum_range (fun ℓ => (n - (ℓ + 1) - 1) * 2 + 1),
    ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr (by simp) fun ℓ _ => ?_
  rw [add_comm 1 ℓ]
  ring

/-- **Binary segmentation selects a polyhedral cone** (Hyun, Lin, G'Sell and Tibshirani 2021,
Proposition 1). For feasible locations `b_{1:k}`, distinct elements of `{1, …, n - 1}`, and
directions `d_{1:k} ∈ {-1, +1}ᵏ`, there is a matrix `Γ` with `∑_{ℓ=1}^{k} (2 (n - ℓ - 1) + 1)`
rows, none of them zero, such that for every tie-breaking rule and every value of `sign 0`
`{y : Γ y > 0} ⊆ {y : M^{BS}_{1:k}(y) = {b_{1:k}, d_{1:k}}} ⊆ {y : Γ y ≥ 0}` (componentwise),
where `M^{BS}_{1:k}` is `k`-step binary segmentation (`model`). The selection event need not
equal the closed cone `{y : Γ y ≥ 0}`: the two can differ on the hyperplanes `{y : γᵀ y = 0}`, one
for each row `γ` of `Γ`, where ties occur. They agree outside these hyperplanes, so almost
everywhere: their symmetric difference is Lebesgue-null. The matrix is explicit: its rows are
those of `selectionRow`, listed through an equivalence `e` of their indices with `Fin` of the row
count. The source states exact equality with the closed cone and `2 ∑_{ℓ=1}^{k} (n - ℓ - 1)`
rows; ties and steps with no competitor break exact equality, hence the two inclusions and the
sign rows. The selection event of infeasible locations is empty (`selectionEvent_eq_empty`). -/
theorem exists_polyhedral_selectionEvent (b : Fin k → ℕ) (d : Fin k → ℤˣ)
    (hb : Function.Injective b) (hbn : ∀ ℓ, b ℓ ∈ Icc 1 (n - 1)) :
    ∃ Γ : Matrix (Fin (∑ ℓ ∈ Icc 1 k, (2 * (n - ℓ - 1) + 1))) (Fin n) ℝ,
      (∃ e : (Σ ℓ : Fin k, Option (competitors n b ℓ × Bool)) ≃
          Fin (∑ ℓ ∈ Icc 1 k, (2 * (n - ℓ - 1) + 1)),
        ∀ i, Γ i = selectionRow n b d (e.symm i)) ∧
      (∀ i, Γ i ≠ 0) ∧ ∀ (rule : TieBreak) (sign0 : ℤˣ),
        {y | ∀ i, 0 < (Γ *ᵥ y) i} ⊆ selectionEvent n rule sign0 b d ∧
        selectionEvent n rule sign0 b d ⊆ {y | ∀ i, 0 ≤ (Γ *ᵥ y) i} ∧
        symmDiff (selectionEvent n rule sign0 b d) {y | ∀ i, 0 ≤ (Γ *ᵥ y) i} ⊆
          ⋃ i, {y | (Γ *ᵥ y) i = 0} ∧
        volume (symmDiff (selectionEvent n rule sign0 b d) {y | ∀ i, 0 ≤ (Γ *ᵥ y) i}) = 0 := by
  let e := Fintype.equivFinOfCardEq (card_selectionRow_index (n := n) hb hbn)
  let Γ : Matrix (Fin (∑ ℓ ∈ Icc 1 k, (2 * (n - ℓ - 1) + 1))) (Fin n) ℝ :=
    Matrix.of fun i => selectionRow n b d (e.symm i)
  have hΓ : ∀ i y, (Γ *ᵥ y) i = selectionRow n b d (e.symm i) ⬝ᵥ y := fun _ _ => rfl
  have hrow : ∀ i, Γ i ≠ 0 := fun i => selectionRow_ne_zero hb hbn d (e.symm i)
  refine ⟨Γ, ⟨e, fun _ => rfl⟩, hrow, fun rule sign0 => ?_⟩
  have hlow : {y | ∀ i, 0 < (Γ *ᵥ y) i} ⊆ selectionEvent n rule sign0 b d := fun y hy =>
    mem_selectionEvent_of_pos hb hbn d rule sign0 fun r => by
      simpa [hΓ] using hy (e r)
  have hup : selectionEvent n rule sign0 b d ⊆ {y | ∀ i, 0 ≤ (Γ *ᵥ y) i} := fun y hy i => by
    rw [hΓ]
    exact selectionRow_dotProduct_nonneg hb hbn d hy _
  have hsub : symmDiff (selectionEvent n rule sign0 b d) {y | ∀ i, 0 ≤ (Γ *ᵥ y) i} ⊆
      ⋃ i, {y | (Γ *ᵥ y) i = 0} := by
    intro y hy
    rw [Set.mem_symmDiff] at hy
    rcases hy with ⟨hE, hC⟩ | ⟨hC, hE⟩
    · exact absurd (hup hE) hC
    · obtain ⟨i, hi⟩ := not_forall.1 fun h => hE (hlow h)
      exact Set.mem_iUnion.2 ⟨i, le_antisymm (not_lt.1 hi) (hC i)⟩
  refine ⟨hlow, hup, hsub, measure_mono_null hsub (measure_iUnion_null fun i => ?_)⟩
  -- Each hyperplane is the kernel of the nonzero linear form `y ↦ (Γ *ᵥ y) i`.
  have hker : {y | (Γ *ᵥ y) i = 0} =
      (LinearMap.ker ((LinearMap.proj i).comp Γ.mulVecLin) : Set (Fin n → ℝ)) := by
    ext y
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp,
      Function.comp_apply, Matrix.mulVecLin_apply, LinearMap.coe_proj, Function.eval]
  rw [hker]
  refine Measure.addHaar_submodule volume _ fun htop => hrow i ?_
  have : Γ i ∈ LinearMap.ker ((LinearMap.proj i).comp Γ.mulVecLin) := by
    rw [htop]; exact Submodule.mem_top
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply,
    LinearMap.coe_proj, Function.eval] at this
  exact dotProduct_self_eq_zero.1 this

end MathlibExt.Probability.Statistics.BinarySegmentation
