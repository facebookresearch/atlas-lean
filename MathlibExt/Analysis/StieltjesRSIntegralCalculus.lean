/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.StieltjesRSIntegral
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Calculus for the Riemann–Stieltjes integral

Additivity over adjacent intervals, integration by parts, and existence of `∫ₐᵇ f dh` for an
integrand `f` of bounded variation against a regulated integrator `h` with no common
discontinuity on the same side (Hildebrandt), for the refinement (Moore–Pollard) Riemann–Stieltjes
integral `HasRSIntegral` of `MathlibExt.Analysis.StieltjesRSIntegral`. The results are stated for
`HasRSIntegral` and `RSIntegrable` and use that file's sums, partition constructions, uniqueness,
linearity and Cauchy criterion.

**Regulated integrators.** A regulated function on `[a, b]` is stated by its defining property:
a right limit at every point of `[a, b)` and a left limit at every point of `(a, b]`. "No common
discontinuity" means that at every point of `[a, b]` at least one of `f`, `h` is continuous within
`[a, b]`. The integral does not exist in general when `f` and `h` jump on the same side at the same
point (the test file of `StieltjesRSIntegral.lean`: `f = h = 𝟙[1, ∞)` on `[0, 2]`).

**One-sided condition.** "No common discontinuity on the same side" means that at every
`x ∈ [a, b]` one of `f`, `h` is right-continuous at `x` (`ContinuousWithinAt · ([a, b] ∩ [x, ∞)) x`)
and one of `f`, `h` is left-continuous at `x` (`ContinuousWithinAt · ([a, b] ∩ (-∞, x]) x`); the
right condition is vacuous at `b` and the left one at `a`. It is implied by the two-sided
condition, and it also allows a common jump on opposite sides: for `f = 𝟙(1, ∞)` (left-continuous)
and `h = 𝟙[1, ∞)` (right-continuous) on `[0, 2]`, both jump at `1`, the two-sided condition fails,
and `∫₀² f dh = 0` exists. In particular `∫ₐᵇ f dh` exists for left-continuous `f` of bounded
variation against right-continuous regulated `h`.

**The Duhamel bridge is not covered.** The bridge integrates the kernel
`s ↦ P(A)(0, s) · P(B)(s, t]` against `B - A`. Even with the first factor left-continuous (a product
over the open interval `(0, s)`), at a jump `c` of `B` the factor `P(B)(s, t]` contains the jump for
`s < c` but not at `s = c`, so the kernel is discontinuous from the left at `c`, the same side on
which the càdlàg integrator `B - A` jumps. Neither the two-sided condition nor the one-sided
condition here applies (see also `StieltjesRSIntegral.lean`).

## Main results

* `HasRSIntegral.add_adjacent`: `∫ₐᶜ f dh = I` and `∫_c^b f dh = J` give `∫ₐᵇ f dh = I + J`.
* `HasRSIntegral.rsIntegrable_left`, `HasRSIntegral.rsIntegrable_right`,
  `HasRSIntegral.exists_split`: if `∫ₐᵇ f dh` exists and `a ≤ c ≤ b`, then `∫ₐᶜ f dh` and
  `∫_c^b f dh` exist and add up to it.
* `HasRSIntegral.integration_by_parts`: `∫ₐᵇ f dh = I` gives
  `∫ₐᵇ h df = f(b) h(b) - f(a) h(a) - I`.
* `rsIntegrable_of_regulated_of_monotoneOn_oneSided`: `∫ₐᵇ g dV` exists for regulated `g` and
  monotone `V` without common discontinuities on the same side.
* `rsIntegrable_of_regulated_of_boundedVariationOn_oneSided`: the same for `V` of bounded variation.
* `rsIntegrable_of_boundedVariationOn_of_regulated_oneSided`: `∫ₐᵇ f dh` exists for `f` of bounded
  variation and regulated `h` without common discontinuities on the same side.
* `rsIntegrable_of_boundedVariationOn_of_regulated_of_leftContinuous`: the case of left-continuous
  `f` and right-continuous `h`.
* `rsIntegrable_of_regulated_of_monotoneOn`, `rsIntegrable_of_regulated_of_boundedVariationOn`,
  `rsIntegrable_of_boundedVariationOn_of_regulated`: the two-sided forms (no common discontinuity),
  as corollaries.

## Proof outline

Partitions are cut and glued through one private construction: a monotone sequence
`a = s₀ ≤ ⋯ ≤ s_N = b` with tags `sᵢ ≤ τᵢ ≤ sᵢ₊₁` (repetitions allowed) yields a tagged partition
with points `{sᵢ}` and the same Riemann–Stieltjes sums. Integration by parts is the termwise
identity `h(ξ)(f(t') - f(t)) + f(t)(h(ξ) - h(t)) + f(t')(h(t') - h(ξ)) = f(t')h(t') - f(t)h(t)`
applied to the interleaved sequence `t₀ ≤ ξ₀ ≤ t₁ ≤ ⋯ ≤ tₙ` tagged by the `tₖ`. For existence,
a compactness argument gives a finite set `S` off which `g` oscillates by at most `ε`. At a point
`e ∈ S` where `g` is not right-continuous, `V` is right-continuous, so the window `[e, e + ρ]`
carries little `V`-mass; symmetrically `[e - ρ, e]` where `g` is not left-continuous. A subinterval
of a fine partition starting at `e` is either a right window or one on which `g` stays close to
`g e`, and likewise for one ending at `e`. The refinement estimate then gives the Cauchy criterion
`rsIntegrable_of_cauchy`. The bounded-variation case follows from the decomposition
`f = V - (V - f)` with `V` the variation function, which is right- (left-) continuous wherever `f`
is (`BoundedVariationOn.continuousWithinAt_variationOnFromTo_inter_Ici`, `_inter_Iic`), and the
regulated-integrator case follows by integration by parts.

## Not covered

* Necessity of the one-sided condition in general: only the example `f = h = 𝟙[1, ∞)` on `[0, 2]`
  (a common jump on the left, where the integral does not exist) is checked, in the test files.
* The Duhamel operator and the Ψ-CLM bridge (whose kernel jumps on the same side as its
  integrator, see above).

## Source receipt

T. M. Apostol, *Mathematical Analysis*, 2nd ed. (1974), Chapter 7: Definition 7.1 (refinement
form), Theorem 7.4 (additivity: if two of `∫ₐᶜ`, `∫_c^b`, `∫ₐᵇ` exist, so does the third, with
sum), Theorem 7.6 (integration by parts), and Theorem 7.27 (existence for a continuous integrand
against a bounded-variation integrator) for the shape of the existence argument. Existence of the
refinement integral for regulated functions without common discontinuities on the same side:
T. H. Hildebrandt, "Definitions of Stieltjes integrals of the Riemann type", *Amer. Math. Monthly*
45 (1938), 265–278. Regulated functions are uniform limits of step functions: J. Dieudonné,
*Foundations of Modern Analysis* (1960), §7.6. Reused: from `StieltjesRSIntegral.lean`, `rsSum`,
`HasRSIntegral`, `RSIntegrable`, `rsSum_eq_sum_range`, `Partition.pointN`, `TaggedPartition.tagN`,
`Partition.ofFinset`, `Partition.common`, `Partition.leftTag`, `HasRSIntegral.unique`,
`HasRSIntegral.sub_right` and `rsIntegrable_of_cauchy`; Mathlib's `variationOnFromTo` (monotone
decomposition and its one-sided continuity) and `IsCompact.elim_nhds_subcover`; Atlas's
`Partition`, `TaggedPartition` and `IsRefinement`. Proved here: everything else. The private
refinement estimate `abs_rsSum_sub_le_sum_of_isRefinement` generalizes
`abs_rsSum_sub_le_of_isRefinement` to per-subinterval bounds `ωₖ`, which the windowed bound in the
existence proof needs; its index bookkeeping restates private helpers of `StieltjesRSIntegral.lean`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Integration

open Finset Set Filter Topology

/-! ### Partitions: points, cutting and gluing -/

section Partitions

variable {a b c : ℝ}

private theorem pointN_lt (P : Partition a b) {i j : ℕ} (hij : i < j) (hj : j ≤ P.n) :
    P.pointN i < P.pointN j := by
  have h := P.ordered (show (⟨i, by omega⟩ : Fin (P.n + 1)) < ⟨j, by omega⟩ from
    Fin.mk_lt_mk.mpr hij)
  rw [← P.pointN_fin, ← P.pointN_fin] at h
  exact h

private theorem mem_pointSet_iff (P : Partition a b) {x : ℝ} :
    x ∈ P.pointSet ↔ ∃ i ≤ P.n, P.pointN i = x := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, Nat.le_of_lt_succ i.isLt, P.pointN_fin i⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, (P.pointN_fin ⟨i, Nat.lt_succ_of_le hi⟩).symm⟩

private theorem mem_Icc_of_mem_pointSet (P : Partition a b) {x : ℝ} (hx : x ∈ P.pointSet) :
    x ∈ Icc a b := by
  obtain ⟨i, rfl⟩ := hx
  exact P.points_mem_Icc i

/-- No point of a partition lies strictly inside one of its subintervals. -/
private theorem le_or_ge_of_mem_pointSet (P : Partition a b) {k : ℕ} {x : ℝ}
    (hx : x ∈ P.pointSet) : x ≤ P.pointN k ∨ P.pointN (k + 1) ≤ x := by
  obtain ⟨i, -, rfl⟩ := (mem_pointSet_iff P).mp hx
  rcases le_or_gt i k with hik | hik
  · exact Or.inl (P.monotone_pointN hik)
  · exact Or.inr (P.monotone_pointN hik)

/-- The partition of `[a, a]` with no subintervals. -/
private def trivialPart (a : ℝ) : TaggedPartition a a where
  n := 0
  points _ := a
  ordered i j hij := absurd hij (by have := i.isLt; have := j.isLt; rw [Fin.lt_def]; omega)
  first := rfl
  last := rfl
  tags i := i.elim0
  tag_mem i := i.elim0

/-- Transport a tagged partition along an equality of right endpoints. -/
private def castRight (T : TaggedPartition a b) {b' : ℝ} (hb : b = b') : TaggedPartition a b' where
  n := T.n
  points := T.points
  ordered := T.ordered
  first := T.first
  last := hb ▸ T.last
  tags := T.tags
  tag_mem := T.tag_mem

/-- Append the subinterval `[c, b]` with tag `τ` to a tagged partition of `[a, c]`. -/
private def append (T : TaggedPartition a c) (hcb : c < b) (τ : ℝ) (hτ : c ≤ τ ∧ τ ≤ b) :
    TaggedPartition a b where
  n := T.n + 1
  points := Fin.lastCases b T.points
  ordered := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_castSucc, Fin.succ_last, Fin.lastCases_last, T.last]
      exact hcb
    | cast j =>
      simp only [Fin.lastCases_castSucc, Fin.succ_castSucc]
      exact T.ordered Fin.castSucc_lt_succ
  first := by
    rw [← Fin.castSucc_zero, Fin.lastCases_castSucc]
    exact T.first
  last := Fin.lastCases_last
  tags := Fin.lastCases τ T.tags
  tag_mem i := by
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.lastCases_castSucc, Fin.succ_last, Fin.lastCases_last, T.last]
      exact hτ
    | cast j =>
      simp only [Fin.lastCases_castSucc, Fin.succ_castSucc]
      exact T.tag_mem j

private theorem append_sum (T : TaggedPartition a c) (hcb : c < b) (τ : ℝ) (hτ : c ≤ τ ∧ τ ≤ b)
    (f h : ℝ → ℝ) : rsSum f h (append T hcb τ hτ) = rsSum f h T + f τ * (h b - h c) := by
  unfold rsSum
  change ∑ i : Fin (T.n + 1), f (Fin.lastCases τ T.tags i) *
    (h (Fin.lastCases (motive := fun _ => ℝ) b T.points i.succ) -
      h (Fin.lastCases (motive := fun _ => ℝ) b T.points i.castSucc)) = _
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.succ_castSucc, Fin.lastCases_last, Fin.succ_last, T.last]

private theorem append_pointSet (T : TaggedPartition a c) (hcb : c < b) (τ : ℝ)
    (hτ : c ≤ τ ∧ τ ≤ b) : (append T hcb τ hτ).pointSet = insert b T.pointSet := by
  ext x
  change x ∈ Set.range (Fin.lastCases (motive := fun _ => ℝ) b T.points) ↔ _
  simp only [Set.mem_range, Set.mem_insert_iff, Partition.pointSet, Fin.exists_fin_succ',
    Fin.lastCases_castSucc, Fin.lastCases_last]
  constructor
  · rintro (h | h)
    · exact Or.inr h
    · exact Or.inl h.symm
  · rintro (h | h)
    · exact Or.inr h.symm
    · exact Or.inl h

/-- **Tagged partitions from monotone sequences.** A finite sequence `a = s₀ ≤ s₁ ≤ ⋯ ≤ s_N = b`
(repetitions allowed) with tags `sᵢ ≤ τᵢ ≤ sᵢ₊₁` yields a tagged partition of `[a, b]` whose points
are the values `sᵢ` and whose Riemann–Stieltjes sums are those of the sequence: the zero-length
subintervals contribute nothing. -/
private theorem exists_of_seq (N : ℕ) : ∀ {b : ℝ} (s τ : ℕ → ℝ), s 0 = a → s N = b →
    (∀ i < N, s i ≤ τ i ∧ τ i ≤ s (i + 1)) →
    ∃ T : TaggedPartition a b, (∀ x, x ∈ T.pointSet ↔ ∃ i ≤ N, s i = x) ∧ ∀ f h : ℝ → ℝ,
      rsSum f h T = ∑ i ∈ range N, f (τ i) * (h (s (i + 1)) - h (s i)) := by
  induction N with
  | zero =>
    intro b s τ h0 hN _
    have hab : a = b := h0.symm.trans hN
    subst hab
    refine ⟨trivialPart a, fun x => ?_, fun f h => by simp [rsSum, trivialPart]⟩
    simp only [Partition.pointSet, trivialPart, Set.mem_range, Nat.le_zero, exists_eq_left, h0]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨0, h⟩⟩
  | succ N ih =>
    intro b s τ h0 hN hτ
    obtain ⟨T0, hT0set, hT0sum⟩ := ih s τ h0 rfl (fun i hi => hτ i (by omega))
    obtain ⟨h1, h2⟩ := hτ N (by omega)
    rcases (h1.trans h2).lt_or_eq with hlt | heq
    · refine ⟨append T0 (hN ▸ hlt) (τ N) ⟨h1, hN ▸ h2⟩, fun x => ?_, fun f h => ?_⟩
      · rw [append_pointSet, Set.mem_insert_iff, hT0set]
        constructor
        · rintro (rfl | ⟨i, hi, rfl⟩)
          · exact ⟨N + 1, le_rfl, hN⟩
          · exact ⟨i, by omega, rfl⟩
        · rintro ⟨i, hi, rfl⟩
          rcases Nat.lt_or_eq_of_le hi with hi | rfl
          · exact Or.inr ⟨i, by omega, rfl⟩
          · exact Or.inl hN
      · rw [append_sum, hT0sum, sum_range_succ, hN]
    · refine ⟨castRight T0 (heq.trans hN), fun x => ?_, fun f h => ?_⟩
      · change x ∈ T0.pointSet ↔ _
        rw [hT0set]
        constructor
        · rintro ⟨i, hi, rfl⟩
          exact ⟨i, by omega, rfl⟩
        · rintro ⟨i, hi, rfl⟩
          rcases Nat.lt_or_eq_of_le hi with hi | rfl
          · exact ⟨i, by omega, rfl⟩
          · exact ⟨N, le_rfl, heq⟩
      · change rsSum f h T0 = _
        rw [hT0sum, sum_range_succ, ← heq, sub_self, mul_zero, add_zero]

/-- **Gluing.** Tagged partitions of `[a, c]` and `[c, b]` glue to a tagged partition of `[a, b]`
with the union of the points and the sum of the Riemann–Stieltjes sums. -/
private theorem exists_glue (T₁ : TaggedPartition a c) (T₂ : TaggedPartition c b) :
    ∃ T : TaggedPartition a b, (∀ x, x ∈ T.pointSet ↔ x ∈ T₁.pointSet ∨ x ∈ T₂.pointSet) ∧
      ∀ f h : ℝ → ℝ, rsSum f h T = rsSum f h T₁ + rsSum f h T₂ := by
  set n₁ := T₁.n
  set n₂ := T₂.n
  set s : ℕ → ℝ := fun i =>
    if i ≤ n₁ then T₁.toPartition.pointN i else T₂.toPartition.pointN (i - n₁)
  set τ : ℕ → ℝ := fun i => if i < n₁ then T₁.tagN i else T₂.tagN (i - n₁)
  have hs₁ : ∀ i ≤ n₁, s i = T₁.toPartition.pointN i := fun i hi => by simp [s, hi]
  have hs₂ : ∀ i, n₁ ≤ i → s i = T₂.toPartition.pointN (i - n₁) := by
    intro i hi
    rcases hi.lt_or_eq with hi | rfl
    · simp [s, not_le.mpr hi]
    · rw [hs₁ _ le_rfl, Nat.sub_self, Partition.pointN_zero, Partition.pointN_of_le _ le_rfl]
  have hτ₁ : ∀ i < n₁, τ i = T₁.tagN i := fun i hi => by simp [τ, hi]
  have hτ₂ : ∀ i, n₁ ≤ i → τ i = T₂.tagN (i - n₁) := fun i hi => by simp [τ, not_lt.mpr hi]
  have h0 : s 0 = a := by rw [hs₁ 0 (Nat.zero_le _), Partition.pointN_zero]
  have hN : s (n₁ + n₂) = b := by
    rw [hs₂ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left, Partition.pointN_of_le _ le_rfl]
  have htag : ∀ i < n₁ + n₂, s i ≤ τ i ∧ τ i ≤ s (i + 1) := by
    intro i hi
    rcases lt_or_ge i n₁ with h | h
    · rw [hs₁ i h.le, hs₁ (i + 1) h, hτ₁ i h]
      exact T₁.tagN_mem h
    · rw [hs₂ i h, hs₂ (i + 1) (by omega), hτ₂ i h, show i + 1 - n₁ = i - n₁ + 1 by omega]
      exact T₂.tagN_mem (by omega)
  obtain ⟨T, hTset, hTsum⟩ := exists_of_seq (n₁ + n₂) s τ h0 hN htag
  refine ⟨T, fun x => ?_, fun f h => ?_⟩
  · rw [hTset, mem_pointSet_iff, mem_pointSet_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      rcases le_or_gt i n₁ with h | h
      · exact Or.inl ⟨i, h, (hs₁ i h).symm⟩
      · exact Or.inr ⟨i - n₁, by omega, (hs₂ i h.le).symm⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact ⟨i, by omega, hs₁ i hi⟩
      · exact ⟨n₁ + i, by omega, by rw [hs₂ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left]⟩
  · rw [hTsum, sum_range_add, rsSum_eq_sum_range, rsSum_eq_sum_range]
    congr 1
    · refine sum_congr rfl fun i hi => ?_
      have hi := Finset.mem_range.mp hi
      rw [hτ₁ i hi, hs₁ i hi.le, hs₁ (i + 1) hi]
    · refine sum_congr rfl fun i _ => ?_
      rw [hτ₂ _ (Nat.le_add_right _ _), hs₂ _ (Nat.le_add_right _ _),
        hs₂ _ (by omega), Nat.add_sub_cancel_left, show n₁ + i + 1 - n₁ = i + 1 by omega]

/-- **Splitting.** A tagged partition of `[a, b]` splits at any of its points into tagged partitions
of the two subintervals. -/
private theorem exists_split_at (T : TaggedPartition a b) {m : ℕ} (hm : m ≤ T.n) :
    ∃ (T₁ : TaggedPartition a (T.toPartition.pointN m))
      (T₂ : TaggedPartition (T.toPartition.pointN m) b),
      (∀ x, x ∈ T₁.pointSet ↔ x ∈ T.pointSet ∧ x ≤ T.toPartition.pointN m) ∧
      (∀ x, x ∈ T₂.pointSet ↔ x ∈ T.pointSet ∧ T.toPartition.pointN m ≤ x) ∧
      ∀ f h : ℝ → ℝ, rsSum f h T = rsSum f h T₁ + rsSum f h T₂ := by
  set p := T.toPartition.pointN
  obtain ⟨T₁, h1set, h1sum⟩ := exists_of_seq m p T.tagN T.toPartition.pointN_zero rfl
    (fun i hi => T.tagN_mem (by omega))
  obtain ⟨T₂, h2set, h2sum⟩ := exists_of_seq (a := p m) (b := b) (T.n - m) (fun i => p (m + i))
    (fun i => T.tagN (m + i)) (by simp)
    (by rw [Nat.add_sub_cancel' hm]; exact Partition.pointN_of_le _ le_rfl)
    (fun i hi => by rw [← add_assoc]; exact T.tagN_mem (by omega))
  refine ⟨T₁, T₂, fun x => ?_, fun x => ?_, fun f h => ?_⟩
  · rw [h1set, mem_pointSet_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by omega, rfl⟩, Partition.monotone_pointN _ hi⟩
    · rintro ⟨⟨i, hi, rfl⟩, hle⟩
      refine ⟨i, ?_, rfl⟩
      by_contra hmi
      exact absurd hle (not_le.mpr (pointN_lt _ (by omega) hi))
  · rw [h2set, mem_pointSet_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨m + i, by omega, rfl⟩, Partition.monotone_pointN _ (Nat.le_add_right _ _)⟩
    · rintro ⟨⟨i, hi, rfl⟩, hle⟩
      have hmi : m ≤ i := by
        by_contra hmi
        exact absurd hle (not_le.mpr (pointN_lt _ (by omega) (by omega)))
      exact ⟨i - m, by omega, by rw [Nat.add_sub_cancel' hmi]⟩
  · rw [h1sum, h2sum, rsSum_eq_sum_range, ← Nat.add_sub_cancel' hm, sum_range_add]
    simp only [Nat.add_sub_cancel' hm, add_assoc, p]

end Partitions

private theorem sum_range_two_mul (F : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ range (2 * n), F i = ∑ k ∈ range n, (F (2 * k) + F (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ]
    ring

/-! ### Refinement estimate against a monotone integrator -/

section Refinement

variable {a b : ℝ}

/-- The positions of the points of `P` among the points of a refinement `Q`. -/
private theorem exists_index_of_isRefinement {P Q : Partition a b} (href : Q.IsRefinement P) :
    ∃ ψ : ℕ → ℕ, Monotone ψ ∧ ψ 0 = 0 ∧ ψ P.n = Q.n ∧ ∀ k, Q.pointN (ψ k) = P.pointN k := by
  have hex : ∀ k : ℕ, ∃ j : ℕ, j ≤ Q.n ∧ Q.pointN j = P.pointN k := by
    intro k
    rcases le_or_gt k P.n with hk | hk
    · obtain ⟨j, hj⟩ := href ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩
      refine ⟨j, Nat.le_of_lt_succ j.isLt, ?_⟩
      rw [Q.pointN_fin, hj, ← P.pointN_fin]
    · exact ⟨Q.n, le_rfl, by rw [Q.pointN_of_le le_rfl, P.pointN_of_le hk.le]⟩
  choose ψ hψle hψ using hex
  refine ⟨ψ, fun k k' hkk' => Q.le_of_pointN_le (hψle k) (hψle k') ?_, ?_, ?_, hψ⟩
  · rw [hψ, hψ]; exact P.monotone_pointN hkk'
  · exact Nat.le_zero.mp (Q.le_of_pointN_le (hψle 0) (Nat.zero_le _)
      (by rw [hψ, P.pointN_zero, Q.pointN_zero]))
  · refine le_antisymm (hψle _) (Q.le_of_pointN_le le_rfl (hψle _) ?_)
    rw [hψ, P.pointN_of_le le_rfl, Q.pointN_of_le le_rfl]

private theorem sum_range_eq_sum_sum_Ico (G : ℕ → ℝ) {ψ : ℕ → ℕ} (hψ : Monotone ψ)
    (h0 : ψ 0 = 0) (m : ℕ) :
    ∑ j ∈ range (ψ m), G j = ∑ k ∈ range m, ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), G j := by
  induction m with
  | zero => simp [h0]
  | succ m ih => rw [sum_range_succ, ← ih, sum_range_add_sum_Ico _ (hψ (Nat.le_succ m))]

private theorem sum_Ico_sub_eq (g : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ j ∈ Ico m n, (g (j + 1) - g j) = g n - g m := by
  rw [sum_Ico_eq_sub _ hmn, sum_range_sub, sum_range_sub]; ring

/-- **Refinement estimate.** Let `V` be monotone on `[a, b]` and let `R` refine the tagged partition
`T`. If `|g (ξₖ) - g x| ≤ ωₖ` whenever `x` lies in the `k`-th subinterval of `T` (with tag `ξₖ`),
then the Riemann–Stieltjes sums over `T` and `R` differ by at most `∑ₖ ωₖ (V(xₖ₊₁) - V(xₖ))`. -/
private theorem abs_rsSum_sub_le_sum_of_isRefinement {g V : ℝ → ℝ} (hV : MonotoneOn V (Icc a b))
    (T R : TaggedPartition a b) (href : R.toPartition.IsRefinement T.toPartition) (ω : ℕ → ℝ)
    (hω : ∀ k < T.n, ∀ x ∈ Icc (T.pointN k) (T.pointN (k + 1)), |g (T.tagN k) - g x| ≤ ω k) :
    |rsSum g V T - rsSum g V R| ≤
      ∑ k ∈ range T.n, ω k * (V (T.pointN (k + 1)) - V (T.pointN k)) := by
  obtain ⟨ψ, hψ, hψ0, hψn, hψpt⟩ := exists_index_of_isRefinement href
  set Δ : ℕ → ℝ := fun j => V (R.pointN (j + 1)) - V (R.pointN j)
  have hΔ : ∀ j, 0 ≤ Δ j := fun j =>
    sub_nonneg.mpr (hV (R.toPartition.pointN_mem_Icc _) (R.toPartition.pointN_mem_Icc _)
      (R.monotone_pointN (Nat.le_succ j)))
  have hblock : ∀ k, V (T.pointN (k + 1)) - V (T.pointN k) =
      ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), Δ j := by
    intro k
    rw [sum_Ico_sub_eq (fun j => V (R.pointN j)) (hψ (Nat.le_succ k)), hψpt, hψpt]
  have hR : rsSum g V R =
      ∑ k ∈ range T.n, ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), g (R.tagN j) * Δ j := by
    rw [rsSum_eq_sum_range, ← hψn, sum_range_eq_sum_sum_Ico _ hψ hψ0]
  have hT : rsSum g V T =
      ∑ k ∈ range T.n, ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), g (T.tagN k) * Δ j := by
    rw [rsSum_eq_sum_range]
    refine sum_congr rfl fun k _ => ?_
    rw [hblock, mul_sum]
  have htag : ∀ k ∈ range T.n, ∀ j ∈ Finset.Ico (ψ k) (ψ (k + 1)),
      R.tagN j ∈ Icc (T.pointN k) (T.pointN (k + 1)) := by
    intro k hk j hj
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Ico] at hj
    have hjn : j < R.n := by
      have := hψ (show k + 1 ≤ T.n by omega); rw [hψn] at this; omega
    obtain ⟨h1, h2⟩ := R.tagN_mem hjn
    rw [← hψpt, ← hψpt]
    exact ⟨(R.monotone_pointN hj.1).trans h1, h2.trans (R.monotone_pointN hj.2)⟩
  rw [hT, hR, ← sum_sub_distrib]
  calc |∑ k ∈ range T.n, (∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), g (T.tagN k) * Δ j -
          ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), g (R.tagN j) * Δ j)|
      ≤ ∑ k ∈ range T.n, |∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), g (T.tagN k) * Δ j -
          ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), g (R.tagN j) * Δ j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range T.n, ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), ω k * Δ j := by
        refine sum_le_sum fun k hk => ?_
        rw [← sum_sub_distrib]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
        rw [← sub_mul, abs_mul, abs_of_nonneg (hΔ j)]
        exact mul_le_mul_of_nonneg_right (hω k (Finset.mem_range.mp hk) _ (htag k hk j hj)) (hΔ j)
    _ = ∑ k ∈ range T.n, ω k * (V (T.pointN (k + 1)) - V (T.pointN k)) := by
        refine sum_congr rfl fun k _ => ?_
        rw [← mul_sum, ← hblock]

end Refinement

/-! ### Regulated functions -/

section Regulated

variable {a b : ℝ}

/-- Near each point of `[a, b]`, a function with one-sided limits oscillates by at most `ε` on
each side and is bounded. -/
private theorem exists_local_of_regulated {g : ℝ → ℝ}
    (hgR : ∀ x ∈ Ico a b, ∃ l, Tendsto g (𝓝[>] x) (𝓝 l))
    (hgL : ∀ x ∈ Ioc a b, ∃ l, Tendsto g (𝓝[<] x) (𝓝 l)) {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ∃ δ > 0, ∃ M : ℝ, x ∈ Icc a b →
      (∀ y ∈ Icc a b, ∀ z ∈ Icc a b, x < y → y < x + δ → x < z → z < x + δ →
        |g y - g z| ≤ ε) ∧
      (∀ y ∈ Icc a b, ∀ z ∈ Icc a b, x - δ < y → y < x → x - δ < z → z < x →
        |g y - g z| ≤ ε) ∧
      (∀ y ∈ Icc a b, x - δ < y → y < x + δ → |g y| ≤ M) := by
  by_cases hx : x ∈ Icc a b
  swap
  · exact ⟨1, one_pos, 0, fun h => absurd h hx⟩
  have hR : ∃ δ > 0, ∃ l : ℝ, ∀ y ∈ Icc a b, x < y → y < x + δ → |g y - l| < ε / 2 := by
    rcases lt_or_ge x b with hxb | hxb
    · obtain ⟨l, hl⟩ := hgR x ⟨hx.1, hxb⟩
      have hev : {y | |g y - l| < ε / 2} ∈ 𝓝[>] x := by
        have := (Metric.tendsto_nhds.mp hl) (ε / 2) (by linarith)
        filter_upwards [this] with y hy
        rwa [Real.dist_eq] at hy
      obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
      exact ⟨u - x, sub_pos.mpr hu, l, fun y _ hxy hy => hsub ⟨hxy, by linarith⟩⟩
    · exact ⟨1, one_pos, 0, fun y hy hxy _ => absurd (hy.2.trans hxb) (not_le.mpr hxy)⟩
  have hL : ∃ δ > 0, ∃ l : ℝ, ∀ y ∈ Icc a b, x - δ < y → y < x → |g y - l| < ε / 2 := by
    rcases lt_or_ge a x with hax | hax
    · obtain ⟨l, hl⟩ := hgL x ⟨hax, hx.2⟩
      have hev : {y | |g y - l| < ε / 2} ∈ 𝓝[<] x := by
        have := (Metric.tendsto_nhds.mp hl) (ε / 2) (by linarith)
        filter_upwards [this] with y hy
        rwa [Real.dist_eq] at hy
      obtain ⟨u, hu, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
      exact ⟨x - u, sub_pos.mpr hu, l, fun y _ hxy hy => hsub ⟨by linarith, hy⟩⟩
    · exact ⟨1, one_pos, 0, fun y hy _ hyx => absurd (hax.trans hy.1) (not_le.mpr hyx)⟩
  obtain ⟨δR, hδR, lR, hlR⟩ := hR
  obtain ⟨δL, hδL, lL, hlL⟩ := hL
  refine ⟨min δR δL, lt_min hδR hδL, |lR| + |lL| + |g x| + ε, fun _ => ⟨?_, ?_, ?_⟩⟩
  · intro y hy z hz hxy hy' hxz hz'
    have h1 := hlR y hy hxy (hy'.trans_le (by linarith [min_le_left δR δL]))
    have h2 := hlR z hz hxz (hz'.trans_le (by linarith [min_le_left δR δL]))
    calc |g y - g z| = |(g y - lR) - (g z - lR)| := by ring_nf
      _ ≤ |g y - lR| + |g z - lR| := abs_sub _ _
      _ ≤ ε := by linarith
  · intro y hy z hz hxy hy' hxz hz'
    have h1 := hlL y hy ((by linarith [min_le_right δR δL] : x - δL ≤ x - min δR δL).trans_lt hxy)
      hy'
    have h2 := hlL z hz ((by linarith [min_le_right δR δL] : x - δL ≤ x - min δR δL).trans_lt hxz)
      hz'
    calc |g y - g z| = |(g y - lL) - (g z - lL)| := by ring_nf
      _ ≤ |g y - lL| + |g z - lL| := abs_sub _ _
      _ ≤ ε := by linarith
  · intro y hy hy1 hy2
    rcases lt_trichotomy y x with hyx | rfl | hxy
    · have h1 := hlL y hy ((by linarith [min_le_right δR δL] : x - δL ≤ x - min δR δL).trans_lt
        hy1) hyx
      have : |g y| ≤ |g y - lL| + |lL| := by
        calc |g y| = |(g y - lL) + lL| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      linarith [abs_nonneg lR, abs_nonneg (g x)]
    · linarith [abs_nonneg lR, abs_nonneg lL]
    · have h1 := hlR y hy hxy (hy2.trans_le (by linarith [min_le_left δR δL]))
      have : |g y| ≤ |g y - lR| + |lR| := by
        calc |g y| = |(g y - lR) + lR| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      linarith [abs_nonneg lL, abs_nonneg (g x)]

/-- **Regulated functions are uniformly approximable by step functions.** If `g` has a right limit
at every point of `[a, b)` and a left limit at every point of `(a, b]`, then `g` is bounded on
`[a, b]`, and for every `ε > 0` there is a finite set `S ⊆ [a, b]` containing `a` and `b` such that
`|g x - g y| ≤ ε` whenever `[x, y] ⊆ [a, b]` contains no point of `S`. -/
private theorem exists_finset_of_regulated {g : ℝ → ℝ} (hab : a ≤ b)
    (hgR : ∀ x ∈ Ico a b, ∃ l, Tendsto g (𝓝[>] x) (𝓝 l))
    (hgL : ∀ x ∈ Ioc a b, ∃ l, Tendsto g (𝓝[<] x) (𝓝 l)) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℝ, ∃ B : ℝ, (∀ s ∈ S, s ∈ Icc a b) ∧ a ∈ S ∧ b ∈ S ∧
      (∀ x ∈ Icc a b, |g x| ≤ B) ∧
      ∀ x y, a ≤ x → x ≤ y → y ≤ b → (∀ s ∈ S, s ∉ Icc x y) → |g x - g y| ≤ ε := by
  choose δ hδ M hloc using exists_local_of_regulated hgR hgL hε
  obtain ⟨t, htmem, hcover⟩ := (isCompact_Icc (a := a) (b := b)).elim_nhds_subcover
    (fun x => Ioo (x - δ x) (x + δ x))
    (fun x _ => Ioo_mem_nhds (by linarith [hδ x]) (by linarith [hδ x]))
  refine ⟨{a, b} ∪ t ∪ t.image (fun x => min b (x + δ x)), ∑ x ∈ t, |M x|, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_image] at hs
    rcases hs with ((rfl | rfl) | hs) | ⟨x, hx, rfl⟩
    · exact ⟨le_rfl, hab⟩
    · exact ⟨hab, le_rfl⟩
    · exact htmem s hs
    · exact ⟨le_min hab (by linarith [(htmem x hx).1, hδ x]), min_le_left _ _⟩
  · simp
  · simp
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (hcover hy)
    exact ((hloc x (htmem x hx)).2.2 y hy hyx.1 hyx.2).trans
      ((le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (M i)) hx))
  · intro x y hax hxy hyb hS
    have hxI : x ∈ Icc a b := ⟨hax, hxy.trans hyb⟩
    have hyI : y ∈ Icc a b := ⟨hax.trans hxy, hyb⟩
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.mp (hcover hxI)
    have hcS : c ∉ Icc x y := hS c (by simp [hc])
    obtain ⟨hR, hL, -⟩ := hloc c (htmem c hc)
    rcases lt_or_ge y c with hyc | hcy
    · exact hL x hxI y hyI hxc.1 (hxy.trans_lt hyc) (by linarith [hxc.1]) hyc
    · have hcx : c < x := by
        by_contra h
        exact hcS ⟨not_lt.mp h, hcy⟩
      have hq : min b (c + δ c) ∉ Icc x y :=
        hS _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hc))
      have hxq : x ≤ min b (c + δ c) := le_min hxI.2 hxc.2.le
      have hyq : y < min b (c + δ c) := by
        by_contra h
        exact hq ⟨hxq, not_lt.mp h⟩
      exact hR x hxI y hyI hcx hxc.2 (hcx.trans_le hxy)
        (hyq.trans_le (min_le_right _ _))

/-- A radius `ρ > 0` such that, if `F` is continuous within `s` at `e`, then `F` is within `κ` of
`F e` on the points of `s` at distance at most `ρ` from `e`. -/
private theorem exists_radius (F : ℝ → ℝ) (s : Set ℝ) (e : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ ρ > 0, ContinuousWithinAt F s e → ∀ x ∈ s, |x - e| ≤ ρ → |F x - F e| ≤ κ := by
  by_cases hF : ContinuousWithinAt F s e
  · obtain ⟨δ, hδ, H⟩ := Metric.continuousWithinAt_iff.mp hF κ hκ
    refine ⟨δ / 2, half_pos hδ, fun _ x hx hxe => ?_⟩
    have := H hx (by rw [Real.dist_eq]; linarith)
    rw [Real.dist_eq] at this
    exact this.le
  · exact ⟨1, one_pos, fun h => absurd h hF⟩
end Regulated


/-! ### Additivity over adjacent intervals -/

section Integral

variable {a b c : ℝ}

/-- **Additivity over adjacent intervals.** If `∫ₐᶜ f dh = I` and `∫_c^b f dh = J`, then
`∫ₐᵇ f dh = I + J`. -/
theorem HasRSIntegral.add_adjacent {f h : ℝ → ℝ} {I J : ℝ} (hI : HasRSIntegral f h a c I)
    (hJ : HasRSIntegral f h c b J) : HasRSIntegral f h a b (I + J) := by
  intro ε hε
  obtain ⟨P₁, hP₁⟩ := hI (ε / 2) (by linarith)
  obtain ⟨P₂, hP₂⟩ := hJ (ε / 2) (by linarith)
  obtain ⟨G, hGset, -⟩ := exists_glue P₁.leftTag P₂.leftTag
  refine ⟨G.toPartition, fun T hT => ?_⟩
  have hc : c ∈ T.pointSet := hT ((hGset c).mpr (Or.inr ⟨0, P₂.first⟩))
  obtain ⟨m, hm, hmc⟩ := (mem_pointSet_iff _).mp hc
  subst hmc
  obtain ⟨T₁, T₂, h1set, h2set, hsum⟩ := exists_split_at T hm
  have h1 := hP₁ T₁ fun x hx =>
    (h1set x).mpr ⟨hT ((hGset x).mpr (Or.inl hx)), (mem_Icc_of_mem_pointSet P₁ hx).2⟩
  have h2 := hP₂ T₂ fun x hx =>
    (h2set x).mpr ⟨hT ((hGset x).mpr (Or.inr hx)), (mem_Icc_of_mem_pointSet P₂ hx).1⟩
  rw [hsum]
  calc |rsSum f h T₁ + rsSum f h T₂ - (I + J)|
      = |(rsSum f h T₁ - I) + (rsSum f h T₂ - J)| := by ring_nf
    _ ≤ |rsSum f h T₁ - I| + |rsSum f h T₂ - J| := abs_add_le _ _
    _ < ε := by linarith

/-- The partition points of `P` that are `≤ c`, together with `c`: a partition of `[a, c]`. -/
private noncomputable def restrictLeft (P : Partition a b) (hac : a ≤ c) : Partition a c :=
  Partition.ofFinset (insert c ((Finset.image P.points Finset.univ).filter (· ≤ c)))
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hac, le_rfl⟩
      · obtain ⟨hx, hxc⟩ := Finset.mem_filter.mp hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨(P.points_mem_Icc i).1, hxc⟩)
    (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨0, mem_univ _, P.first⟩, hac⟩))
    (Finset.mem_insert_self _ _)

/-- The partition points of `P` that are `≥ c`, together with `c`: a partition of `[c, b]`. -/
private noncomputable def restrictRight (P : Partition a b) (hcb : c ≤ b) : Partition c b :=
  Partition.ofFinset (insert c ((Finset.image P.points Finset.univ).filter (c ≤ ·)))
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨le_rfl, hcb⟩
      · obtain ⟨hx, hxc⟩ := Finset.mem_filter.mp hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨hxc, (P.points_mem_Icc i).2⟩)
    (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨Fin.last _, mem_univ _, P.last⟩, hcb⟩))

/-- Every point of `P` is a point of `restrictLeft P` or of `restrictRight P`. -/
private theorem mem_restrict (P : Partition a b) (hac : a ≤ c) (hcb : c ≤ b) {x : ℝ}
    (hx : x ∈ P.pointSet) :
    x ∈ (restrictLeft P hac).pointSet ∨ x ∈ (restrictRight (a := a) P hcb).pointSet := by
  obtain ⟨i, rfl⟩ := hx
  rw [restrictLeft, restrictRight, Partition.pointSet_ofFinset, Partition.pointSet_ofFinset]
  rcases le_total (P.points i) c with h | h
  · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem _ (mem_univ _), h⟩)))
  · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem _ (mem_univ _), h⟩)))

/-- **Restriction to a left subinterval.** If `∫ₐᵇ f dh` exists and `a ≤ c ≤ b`, then
`∫ₐᶜ f dh` exists. -/
theorem HasRSIntegral.rsIntegrable_left {f h : ℝ → ℝ} {I : ℝ} (hI : HasRSIntegral f h a b I)
    (hac : a ≤ c) (hcb : c ≤ b) : RSIntegrable f h a c := by
  refine rsIntegrable_of_cauchy fun ε hε => ?_
  obtain ⟨P, hP⟩ := hI (ε / 2) (by linarith)
  refine ⟨restrictLeft P hac, fun T T' hT hT' => ?_⟩
  obtain ⟨G, hGset, hGsum⟩ := exists_glue T (restrictRight (a := a) P hcb).leftTag
  obtain ⟨G', hG'set, hG'sum⟩ := exists_glue T' (restrictRight (a := a) P hcb).leftTag
  have h1 := hP G fun x hx => by
    rcases mem_restrict P hac hcb hx with h | h
    · exact (hGset x).mpr (Or.inl (hT h))
    · exact (hGset x).mpr (Or.inr h)
  have h2 := hP G' fun x hx => by
    rcases mem_restrict P hac hcb hx with h | h
    · exact (hG'set x).mpr (Or.inl (hT' h))
    · exact (hG'set x).mpr (Or.inr h)
  rw [hGsum, hG'sum] at *
  calc |rsSum f h T - rsSum f h T'|
      = |(rsSum f h T + rsSum f h (restrictRight (a := a) P hcb).leftTag - I) -
          (rsSum f h T' + rsSum f h (restrictRight (a := a) P hcb).leftTag - I)| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ ε := by linarith

/-- **Restriction to a right subinterval.** If `∫ₐᵇ f dh` exists and `a ≤ c ≤ b`, then
`∫_c^b f dh` exists. -/
theorem HasRSIntegral.rsIntegrable_right {f h : ℝ → ℝ} {I : ℝ} (hI : HasRSIntegral f h a b I)
    (hac : a ≤ c) (hcb : c ≤ b) : RSIntegrable f h c b := by
  refine rsIntegrable_of_cauchy fun ε hε => ?_
  obtain ⟨P, hP⟩ := hI (ε / 2) (by linarith)
  refine ⟨restrictRight P hcb, fun T T' hT hT' => ?_⟩
  obtain ⟨G, hGset, hGsum⟩ := exists_glue (restrictLeft (b := b) P hac).leftTag T
  obtain ⟨G', hG'set, hG'sum⟩ := exists_glue (restrictLeft (b := b) P hac).leftTag T'
  have h1 := hP G fun x hx => by
    rcases mem_restrict P hac hcb hx with h | h
    · exact (hGset x).mpr (Or.inl h)
    · exact (hGset x).mpr (Or.inr (hT h))
  have h2 := hP G' fun x hx => by
    rcases mem_restrict P hac hcb hx with h | h
    · exact (hG'set x).mpr (Or.inl h)
    · exact (hG'set x).mpr (Or.inr (hT' h))
  rw [hGsum, hG'sum] at *
  calc |rsSum f h T - rsSum f h T'|
      = |(rsSum f h (restrictLeft (b := b) P hac).leftTag + rsSum f h T - I) -
          (rsSum f h (restrictLeft (b := b) P hac).leftTag + rsSum f h T' - I)| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ ε := by linarith

/-- **Additivity over adjacent intervals (Apostol, Theorem 7.4).** If `∫ₐᵇ f dh = I` and
`a ≤ c ≤ b`, then both `∫ₐᶜ f dh` and `∫_c^b f dh` exist and add up to `I`. -/
theorem HasRSIntegral.exists_split {f h : ℝ → ℝ} {I : ℝ} (hI : HasRSIntegral f h a b I)
    (hac : a ≤ c) (hcb : c ≤ b) :
    ∃ I₁ I₂, HasRSIntegral f h a c I₁ ∧ HasRSIntegral f h c b I₂ ∧ I = I₁ + I₂ := by
  obtain ⟨I₁, h₁⟩ := hI.rsIntegrable_left hac hcb
  obtain ⟨I₂, h₂⟩ := hI.rsIntegrable_right hac hcb
  exact ⟨I₁, I₂, h₁, h₂, hI.unique (h₁.add_adjacent h₂)⟩

/-! ### Integration by parts -/

/-- **Integration by parts (Apostol, Theorem 7.6).** If `∫ₐᵇ f dh = I`, then `∫ₐᵇ h df` exists and
equals `f(b) h(b) - f(a) h(a) - I`. -/
theorem HasRSIntegral.integration_by_parts {f h : ℝ → ℝ} {I : ℝ} (hI : HasRSIntegral f h a b I) :
    HasRSIntegral h f a b (f b * h b - f a * h a - I) := by
  intro ε hε
  obtain ⟨P, hP⟩ := hI ε hε
  refine ⟨P, fun T hT => ?_⟩
  set n := T.n
  set t := T.toPartition.pointN with ht
  set ξ := T.tagN with hξ
  set s : ℕ → ℝ := fun i => if i % 2 = 0 then t (i / 2) else ξ (i / 2) with hs
  set τ : ℕ → ℝ := fun i => if i % 2 = 0 then t (i / 2) else t (i / 2 + 1) with hτ
  have hse : ∀ k, s (2 * k) = t k := fun k => by
    simp only [hs, show 2 * k % 2 = 0 by omega, ↓reduceIte, show 2 * k / 2 = k by omega]
  have hso : ∀ k, s (2 * k + 1) = ξ k := fun k => by
    simp only [hs, show ¬(2 * k + 1) % 2 = 0 by omega, ↓reduceIte,
      show (2 * k + 1) / 2 = k by omega]
  have hτe : ∀ k, τ (2 * k) = t k := fun k => by
    simp only [hτ, show 2 * k % 2 = 0 by omega, ↓reduceIte, show 2 * k / 2 = k by omega]
  have hτo : ∀ k, τ (2 * k + 1) = t (k + 1) := fun k => by
    simp only [hτ, show ¬(2 * k + 1) % 2 = 0 by omega, ↓reduceIte,
      show (2 * k + 1) / 2 = k by omega]
  have hss : ∀ k, s (2 * k + 1 + 1) = t (k + 1) := fun k => by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, hse]
  have h0 : s 0 = a := by rw [show (0 : ℕ) = 2 * 0 from rfl, hse, ht, Partition.pointN_zero]
  have hN : s (2 * n) = b := by rw [hse, ht, Partition.pointN_of_le _ le_rfl]
  have htag : ∀ i < 2 * n, s i ≤ τ i ∧ τ i ≤ s (i + 1) := by
    intro i hi
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [hse, hτe, hso]
      exact ⟨le_rfl, (T.tagN_mem (by omega)).1⟩
    · rw [hso, hτo, hss]
      exact ⟨(T.tagN_mem (by omega)).2, le_rfl⟩
  obtain ⟨T', hT'set, hT'sum⟩ := exists_of_seq (2 * n) s τ h0 hN htag
  have href : T'.toPartition.IsRefinement P := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := (mem_pointSet_iff _).mp (hT hx)
    exact (hT'set _).mpr ⟨2 * k, by omega, hse k⟩
  have key := hP T' href
  have hparts : rsSum h f T = f b * h b - f a * h a - rsSum f h T' := by
    rw [hT'sum, sum_range_two_mul, rsSum_eq_sum_range]
    have htel : ∑ k ∈ range n, (f (t (k + 1)) * h (t (k + 1)) - f (t k) * h (t k)) =
        f b * h b - f a * h a := by
      rw [sum_range_sub (fun k => f (t k) * h (t k)), ht, Partition.pointN_of_le _ le_rfl,
        Partition.pointN_zero]
    rw [← htel, eq_sub_iff_add_eq, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [hτe, hτo, hso, hse, hss]
    ring
  rw [hparts, show f b * h b - f a * h a - rsSum f h T' - (f b * h b - f a * h a - I) =
    -(rsSum f h T' - I) by ring, abs_neg]
  exact key

/-! ### Existence for regulated integrands and integrators -/

/-- **Existence against a monotone integrator, one-sided form (Hildebrandt).** Let `g` have a right
limit at every point of `[a, b)` and a left limit at every point of `(a, b]` (`g` is regulated), and
let `V` be monotone on `[a, b]`. Suppose `g` and `V` have no common discontinuity on the same side:
at every `x ∈ [a, b]`, one of `g`, `V` is right-continuous at `x` (within `[a, b] ∩ [x, ∞)`) and one
of `g`, `V` is left-continuous at `x` (within `[a, b] ∩ (-∞, x]`). Then `∫ₐᵇ g dV` exists. -/
theorem rsIntegrable_of_regulated_of_monotoneOn_oneSided {g V : ℝ → ℝ} (hab : a ≤ b)
    (hgR : ∀ x ∈ Ico a b, ∃ l, Tendsto g (𝓝[>] x) (𝓝 l))
    (hgL : ∀ x ∈ Ioc a b, ∃ l, Tendsto g (𝓝[<] x) (𝓝 l))
    (hV : MonotoneOn V (Icc a b))
    (hright : ∀ x ∈ Icc a b,
      ContinuousWithinAt g (Icc a b ∩ Ici x) x ∨ ContinuousWithinAt V (Icc a b ∩ Ici x) x)
    (hleft : ∀ x ∈ Icc a b,
      ContinuousWithinAt g (Icc a b ∩ Iic x) x ∨ ContinuousWithinAt V (Icc a b ∩ Iic x) x) :
    RSIntegrable g V a b := by
  classical
  refine rsIntegrable_of_cauchy fun ε hε => ?_
  have hVab : 0 ≤ V b - V a := sub_nonneg.mpr (hV ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  set ε₁ := ε / (8 * (V b - V a + 1)) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  obtain ⟨S, B, hSmem, haS, hbS, hB, hosc⟩ := exists_finset_of_regulated hab hgR hgL hε₁pos
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB a ⟨le_rfl, hab⟩)
  set η := ε / (16 * (B + 1) * (S.card + 1)) with hη
  have hηpos : 0 < η := by positivity
  -- one radius serving the four one-sided continuity statements at `e`
  have hρ : ∀ e, ∃ ρ > 0,
      (ContinuousWithinAt g (Icc a b ∩ Ici e) e →
        ∀ x ∈ Icc a b ∩ Ici e, |x - e| ≤ ρ → |g x - g e| ≤ ε₁) ∧
      (ContinuousWithinAt g (Icc a b ∩ Iic e) e →
        ∀ x ∈ Icc a b ∩ Iic e, |x - e| ≤ ρ → |g x - g e| ≤ ε₁) ∧
      (ContinuousWithinAt V (Icc a b ∩ Ici e) e →
        ∀ x ∈ Icc a b ∩ Ici e, |x - e| ≤ ρ → |V x - V e| ≤ η) ∧
      (ContinuousWithinAt V (Icc a b ∩ Iic e) e →
        ∀ x ∈ Icc a b ∩ Iic e, |x - e| ≤ ρ → |V x - V e| ≤ η) := by
    intro e
    obtain ⟨ρ₁, hρ₁, H₁⟩ := exists_radius g (Icc a b ∩ Ici e) e hε₁pos
    obtain ⟨ρ₂, hρ₂, H₂⟩ := exists_radius g (Icc a b ∩ Iic e) e hε₁pos
    obtain ⟨ρ₃, hρ₃, H₃⟩ := exists_radius V (Icc a b ∩ Ici e) e hηpos
    obtain ⟨ρ₄, hρ₄, H₄⟩ := exists_radius V (Icc a b ∩ Iic e) e hηpos
    have h1 : min (min ρ₁ ρ₂) (min ρ₃ ρ₄) ≤ ρ₁ := (min_le_left _ _).trans (min_le_left _ _)
    have h2 : min (min ρ₁ ρ₂) (min ρ₃ ρ₄) ≤ ρ₂ := (min_le_left _ _).trans (min_le_right _ _)
    have h3 : min (min ρ₁ ρ₂) (min ρ₃ ρ₄) ≤ ρ₃ := (min_le_right _ _).trans (min_le_left _ _)
    have h4 : min (min ρ₁ ρ₂) (min ρ₃ ρ₄) ≤ ρ₄ := (min_le_right _ _).trans (min_le_right _ _)
    exact ⟨_, lt_min (lt_min hρ₁ hρ₂) (lt_min hρ₃ hρ₄),
      fun hc x hx hxe => H₁ hc x hx (hxe.trans h1), fun hc x hx hxe => H₂ hc x hx (hxe.trans h2),
      fun hc x hx hxe => H₃ hc x hx (hxe.trans h3), fun hc x hx hxe => H₄ hc x hx (hxe.trans h4)⟩
  choose ρ hρpos hρgR hρgL hρVR hρVL using hρ
  set lo : ℝ → ℝ := fun e => max a (e - ρ e) with hlo
  set hi : ℝ → ℝ := fun e => min b (e + ρ e) with hhi
  have hlo_mem : ∀ e ∈ Icc a b, lo e ∈ Icc a b := fun e he =>
    ⟨le_max_left _ _, max_le hab (by linarith [he.2, hρpos e])⟩
  have hhi_mem : ∀ e ∈ Icc a b, hi e ∈ Icc a b := fun e he =>
    ⟨le_min hab (by linarith [he.1, hρpos e]), min_le_left _ _⟩
  have hlo_le : ∀ e ∈ Icc a b, lo e ≤ e := fun e he => max_le he.1 (by linarith [hρpos e])
  have hle_hi : ∀ e ∈ Icc a b, e ≤ hi e := fun e he => le_min he.2 (by linarith [hρpos e])
  have hlo_dist : ∀ e ∈ Icc a b, |lo e - e| ≤ ρ e := fun e he => by
    rw [abs_of_nonpos (by linarith [hlo_le e he])]
    linarith [le_max_right a (e - ρ e)]
  have hhi_dist : ∀ e ∈ Icc a b, |hi e - e| ≤ ρ e := fun e he => by
    rw [abs_of_nonneg (by linarith [hle_hi e he])]
    linarith [min_le_right b (e + ρ e)]
  set Qs : Finset ℝ := S ∪ S.image lo ∪ S.image hi with hQs
  have hQsmem : ∀ x ∈ Qs, x ∈ Icc a b := by
    intro x hx
    simp only [hQs, Finset.mem_union, Finset.mem_image] at hx
    rcases hx with (hx | ⟨e, he, rfl⟩) | ⟨e, he, rfl⟩
    · exact hSmem x hx
    · exact hlo_mem e (hSmem e he)
    · exact hhi_mem e (hSmem e he)
  set Q := Partition.ofFinset Qs hQsmem (Finset.mem_union_left _ (Finset.mem_union_left _ haS))
    (Finset.mem_union_left _ (Finset.mem_union_left _ hbS))
  -- the windows: `[e, hi e]` where `g` jumps on the right, `[lo e, e]` where it jumps on the left
  set Win : Finset (ℝ × ℝ) :=
    (S.filter fun e => ¬ ContinuousWithinAt g (Icc a b ∩ Ici e) e).image (fun e => (e, hi e)) ∪
      (S.filter fun e => ¬ ContinuousWithinAt g (Icc a b ∩ Iic e) e).image (fun e => (lo e, e))
    with hWin
  have hWin_mem : ∀ w ∈ Win, a ≤ w.1 ∧ w.1 ≤ w.2 ∧ w.2 ≤ b := by
    intro w hw
    simp only [hWin, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hw
    rcases hw with ⟨e, ⟨heS, -⟩, rfl⟩ | ⟨e, ⟨heS, -⟩, rfl⟩
    · have heI := hSmem e heS
      exact ⟨heI.1, hle_hi e heI, (hhi_mem e heI).2⟩
    · have heI := hSmem e heS
      exact ⟨(hlo_mem e heI).1, hlo_le e heI, heI.2⟩
  have hWin_V : ∀ w ∈ Win, V w.2 - V w.1 ≤ η := by
    intro w hw
    simp only [hWin, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hw
    rcases hw with ⟨e, ⟨heS, hgc⟩, rfl⟩ | ⟨e, ⟨heS, hgc⟩, rfl⟩
    · have heI := hSmem e heS
      have := hρVR e ((hright e heI).resolve_left hgc) (hi e) ⟨hhi_mem e heI, hle_hi e heI⟩
        (hhi_dist e heI)
      exact (le_abs_self _).trans this
    · have heI := hSmem e heS
      have := hρVL e ((hleft e heI).resolve_left hgc) (lo e) ⟨hlo_mem e heI, hlo_le e heI⟩
        (hlo_dist e heI)
      change V e - V (lo e) ≤ η
      linarith [neg_abs_le (V (lo e) - V e)]
  have hWin_card : (Win.card : ℝ) ≤ 2 * S.card := by
    have h1 := (Finset.card_union_le _ _).trans
      (add_le_add (Finset.card_image_le (s := S.filter fun e =>
          ¬ ContinuousWithinAt g (Icc a b ∩ Ici e) e) (f := fun e => (e, hi e)))
        (Finset.card_image_le (s := S.filter fun e =>
          ¬ ContinuousWithinAt g (Icc a b ∩ Iic e) e) (f := fun e => (lo e, e))))
    have h2 := Finset.card_filter_le S fun e => ¬ ContinuousWithinAt g (Icc a b ∩ Ici e) e
    have h3 := Finset.card_filter_le S fun e => ¬ ContinuousWithinAt g (Icc a b ∩ Iic e) e
    rw [← hWin] at h1
    exact_mod_cast (show Win.card ≤ 2 * S.card by omega)
  -- the clamped integrators
  set W : ℝ × ℝ → ℝ → ℝ := fun w x => V (max w.1 (min x w.2)) with hW
  have hW_mono : ∀ w ∈ Win, ∀ x y, x ≤ y → W w x ≤ W w y := by
    intro w hw x y hxy
    obtain ⟨h1, h2, h3⟩ := hWin_mem w hw
    have hmem : ∀ z, max w.1 (min z w.2) ∈ Icc a b := fun z =>
      ⟨h1.trans (le_max_left _ _), max_le (h2.trans h3) ((min_le_right _ _).trans h3)⟩
    exact hV (hmem x) (hmem y) (max_le_max le_rfl (min_le_min hxy le_rfl))
  have hW_eq : ∀ (w : ℝ × ℝ) (x : ℝ), w.1 ≤ x → x ≤ w.2 → W w x = V x := by
    intro w x h1 h2
    simp only [hW, min_eq_left h2, max_eq_right h1]
  have hW_b : ∀ w ∈ Win, W w b = V w.2 := by
    intro w hw
    obtain ⟨-, h2, h3⟩ := hWin_mem w hw
    simp only [hW, min_eq_right h3, max_eq_right h2]
  have hW_a : ∀ w ∈ Win, W w a = V w.1 := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hWin_mem w hw
    simp only [hW, min_eq_left (h1.trans h2), max_eq_left h1]
  -- the main estimate
  have hmain : ∀ T : TaggedPartition a b, T.toPartition.IsRefinement Q →
      ∀ R : TaggedPartition a b, R.toPartition.IsRefinement T.toPartition →
        |rsSum g V T - rsSum g V R| ≤ ε / 2 := by
    intro T hTQ R hRT
    set t := T.toPartition.pointN with ht
    have hQT : ∀ x ∈ Qs, x ∈ T.pointSet := fun x hx =>
      hTQ (by rw [Partition.pointSet_ofFinset]; exact Finset.mem_coe.mpr hx)
    have hST : ∀ e ∈ S, e ∈ T.pointSet := fun e he =>
      hQT e (Finset.mem_union_left _ (Finset.mem_union_left _ he))
    have hloT : ∀ e ∈ S, lo e ∈ T.pointSet := fun e he =>
      hQT _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)))
    have hhiT : ∀ e ∈ S, hi e ∈ T.pointSet := fun e he =>
      hQT _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he))
    -- each subinterval of `T` is good or lies in a window
    have hclaim : ∀ k < T.n, (∀ x ∈ Icc (t k) (t (k + 1)), |g (T.tagN k) - g x| ≤ 2 * ε₁) ∨
        ∃ w ∈ Win, w.1 ≤ t k ∧ t (k + 1) ≤ w.2 := by
      intro k hk
      have huv : t k < t (k + 1) := pointN_lt _ (Nat.lt_succ_self k) (by omega)
      have huI := T.toPartition.pointN_mem_Icc k
      have hvI := T.toPartition.pointN_mem_Icc (k + 1)
      have hξ := T.tagN_mem hk
      by_cases hus : t k ∈ S
      · have hhi_gt : t k < hi (t k) :=
          lt_min (huv.trans_le hvI.2) (by linarith [hρpos (t k)])
        have hv_hi : t (k + 1) ≤ hi (t k) :=
          (le_or_ge_of_mem_pointSet T.toPartition (k := k) (hhiT _ hus)).resolve_left
            (not_le.mpr hhi_gt)
        by_cases hgc : ContinuousWithinAt g (Icc a b ∩ Ici (t k)) (t k)
        · left
          intro x hx
          have hd : ∀ y ∈ Icc (t k) (t (k + 1)), |g y - g (t k)| ≤ ε₁ := by
            intro y hy
            refine hρgR _ hgc y ⟨⟨huI.1.trans hy.1, hy.2.trans hvI.2⟩, hy.1⟩ ?_
            rw [abs_of_nonneg (by linarith [hy.1])]
            linarith [hy.2, min_le_right b (t k + ρ (t k)), hhi_dist (t k) huI]
          have h1 := hd (T.tagN k) hξ
          have h2 := hd x hx
          calc |g (T.tagN k) - g x| = |(g (T.tagN k) - g (t k)) - (g x - g (t k))| := by ring_nf
            _ ≤ |g (T.tagN k) - g (t k)| + |g x - g (t k)| := abs_sub _ _
            _ ≤ 2 * ε₁ := by linarith
        · refine Or.inr ⟨(t k, hi (t k)), Finset.mem_union_left _ ?_, le_rfl, hv_hi⟩
          exact Finset.mem_image_of_mem (fun e => (e, hi e)) (Finset.mem_filter.mpr ⟨hus, hgc⟩)
      by_cases hvs : t (k + 1) ∈ S
      · have hlo_lt : lo (t (k + 1)) < t (k + 1) :=
          max_lt (huI.1.trans_lt huv) (by linarith [hρpos (t (k + 1))])
        have hlo_u : lo (t (k + 1)) ≤ t k :=
          (le_or_ge_of_mem_pointSet T.toPartition (k := k) (hloT _ hvs)).resolve_right
            (not_le.mpr hlo_lt)
        by_cases hgc : ContinuousWithinAt g (Icc a b ∩ Iic (t (k + 1))) (t (k + 1))
        · left
          intro x hx
          have hd : ∀ y ∈ Icc (t k) (t (k + 1)), |g y - g (t (k + 1))| ≤ ε₁ := by
            intro y hy
            refine hρgL _ hgc y ⟨⟨huI.1.trans hy.1, hy.2.trans hvI.2⟩, hy.2⟩ ?_
            rw [abs_of_nonpos (by linarith [hy.2])]
            linarith [hy.1, le_max_right a (t (k + 1) - ρ (t (k + 1)))]
          have h1 := hd (T.tagN k) hξ
          have h2 := hd x hx
          calc |g (T.tagN k) - g x|
              = |(g (T.tagN k) - g (t (k + 1))) - (g x - g (t (k + 1)))| := by ring_nf
            _ ≤ |g (T.tagN k) - g (t (k + 1))| + |g x - g (t (k + 1))| := abs_sub _ _
            _ ≤ 2 * ε₁ := by linarith
        · refine Or.inr ⟨(lo (t (k + 1)), t (k + 1)), Finset.mem_union_right _ ?_, hlo_u, le_rfl⟩
          exact Finset.mem_image_of_mem (fun e => (lo e, e)) (Finset.mem_filter.mpr ⟨hvs, hgc⟩)
      · left
        have hfree : ∀ s ∈ S, s ∉ Icc (t k) (t (k + 1)) := by
          intro s hs hmem
          rcases le_or_ge_of_mem_pointSet T.toPartition (k := k) (hST s hs) with h | h
          · have hst : s = t k := le_antisymm h hmem.1
            rw [hst] at hs
            exact hus hs
          · have hst : s = t (k + 1) := le_antisymm hmem.2 h
            rw [hst] at hs
            exact hvs hs
        intro x hx
        have hsub : ∀ y z, y ∈ Icc (t k) (t (k + 1)) → z ∈ Icc (t k) (t (k + 1)) → y ≤ z →
            |g y - g z| ≤ ε₁ := fun y z hy hz hyz =>
          hosc y z (huI.1.trans hy.1) hyz (hz.2.trans hvI.2)
            (fun s hs hmem => hfree s hs ⟨hy.1.trans hmem.1, hmem.2.trans hz.2⟩)
        rcases le_total (T.tagN k) x with h | h
        · linarith [hsub _ _ hξ hx h]
        · rw [abs_sub_comm]; linarith [hsub _ _ hx hξ h]
    set ω : ℕ → ℝ := fun k =>
      if ∀ x ∈ Icc (t k) (t (k + 1)), |g (T.tagN k) - g x| ≤ 2 * ε₁ then 2 * ε₁ else 2 * B
      with hω
    have hωb : ∀ k < T.n, ∀ x ∈ Icc (t k) (t (k + 1)), |g (T.tagN k) - g x| ≤ ω k := by
      intro k hk x hx
      simp only [hω]
      split_ifs with h
      · exact h x hx
      · have hxI : x ∈ Icc a b :=
          ⟨(T.toPartition.pointN_mem_Icc k).1.trans hx.1,
            hx.2.trans (T.toPartition.pointN_mem_Icc (k + 1)).2⟩
        calc |g (T.tagN k) - g x| ≤ |g (T.tagN k)| + |g x| := abs_sub _ _
          _ ≤ 2 * B := by linarith [hB _ (T.tagN_mem_Icc k), hB x hxI]
    have hest := abs_rsSum_sub_le_sum_of_isRefinement hV T R hRT ω hωb
    have hΔ : ∀ k, 0 ≤ V (t (k + 1)) - V (t k) := fun k =>
      sub_nonneg.mpr (hV (T.toPartition.pointN_mem_Icc _) (T.toPartition.pointN_mem_Icc _)
        (T.monotone_pointN (Nat.le_succ k)))
    have hΔW : ∀ w ∈ Win, ∀ k, 0 ≤ W w (t (k + 1)) - W w (t k) := fun w hw k =>
      sub_nonneg.mpr (hW_mono w hw _ _ (T.monotone_pointN (Nat.le_succ k)))
    have hterm : ∀ k ∈ range T.n, ω k * (V (t (k + 1)) - V (t k)) ≤
        2 * ε₁ * (V (t (k + 1)) - V (t k)) +
          2 * B * ∑ w ∈ Win, (W w (t (k + 1)) - W w (t k)) := by
      intro k hk
      have hk := Finset.mem_range.mp hk
      have hsumW : 0 ≤ ∑ w ∈ Win, (W w (t (k + 1)) - W w (t k)) :=
        sum_nonneg fun w hw => hΔW w hw k
      simp only [hω]
      split_ifs with h
      · nlinarith [hΔ k]
      · obtain ⟨w, hw, h1, h2⟩ := (hclaim k hk).resolve_left h
        have hsingle : W w (t (k + 1)) - W w (t k) ≤ ∑ w ∈ Win, (W w (t (k + 1)) - W w (t k)) :=
          Finset.single_le_sum (fun w hw => hΔW w hw k) hw
        rw [hW_eq w _ h1 ((T.monotone_pointN (Nat.le_succ k)).trans h2),
          hW_eq w _ (h1.trans (T.monotone_pointN (Nat.le_succ k))) h2] at hsingle
        nlinarith [hΔ k, hε₁pos]
    have htelV : ∑ k ∈ range T.n, (V (t (k + 1)) - V (t k)) = V b - V a := by
      rw [sum_range_sub (fun k => V (t k)), ht, Partition.pointN_of_le _ le_rfl,
        Partition.pointN_zero]
    have htelW : ∀ w ∈ Win, ∑ k ∈ range T.n, (W w (t (k + 1)) - W w (t k)) =
        V w.2 - V w.1 := by
      intro w hw
      rw [sum_range_sub (fun k => W w (t k)), ht, Partition.pointN_of_le _ le_rfl,
        Partition.pointN_zero, hW_b w hw, hW_a w hw]
    have hsumWin : ∑ w ∈ Win, (V w.2 - V w.1) ≤ 2 * S.card * η := by
      calc ∑ w ∈ Win, (V w.2 - V w.1) ≤ ∑ _w ∈ Win, η := sum_le_sum hWin_V
        _ = Win.card * η := by rw [sum_const, nsmul_eq_mul]
        _ ≤ 2 * S.card * η := by gcongr
    have hbound : ∑ k ∈ range T.n, ω k * (V (t (k + 1)) - V (t k)) ≤
        2 * ε₁ * (V b - V a) + 2 * B * (2 * S.card * η) := by
      calc ∑ k ∈ range T.n, ω k * (V (t (k + 1)) - V (t k))
          ≤ ∑ k ∈ range T.n, (2 * ε₁ * (V (t (k + 1)) - V (t k)) +
              2 * B * ∑ w ∈ Win, (W w (t (k + 1)) - W w (t k))) := sum_le_sum hterm
        _ = 2 * ε₁ * ∑ k ∈ range T.n, (V (t (k + 1)) - V (t k)) +
              2 * B * ∑ w ∈ Win, ∑ k ∈ range T.n, (W w (t (k + 1)) - W w (t k)) := by
            rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_comm]
        _ = 2 * ε₁ * (V b - V a) + 2 * B * ∑ w ∈ Win, (V w.2 - V w.1) := by
            rw [htelV]
            congr 2
            exact sum_congr rfl fun w hw => htelW w hw
        _ ≤ 2 * ε₁ * (V b - V a) + 2 * B * (2 * S.card * η) := by gcongr
    have harith1 : 2 * ε₁ * (V b - V a) ≤ ε / 4 := by
      have : ε₁ * (8 * (V b - V a + 1)) = ε := div_mul_cancel₀ _ (by positivity)
      nlinarith
    have harith2 : 2 * B * (2 * S.card * η) ≤ ε / 4 := by
      have : η * (16 * (B + 1) * (S.card + 1)) = ε := div_mul_cancel₀ _ (by positivity)
      have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
      nlinarith [mul_nonneg hB0 hS0, mul_nonneg (mul_nonneg hB0 hS0) hηpos.le]
    linarith
  refine ⟨Q, fun T T' hT hT' => ?_⟩
  set R := (T.toPartition.common T'.toPartition).leftTag
  have h1 := hmain T hT R (Partition.common_isRefinement_left _ _)
  have h2 := hmain T' hT' R (Partition.common_isRefinement_right _ _)
  calc |rsSum g V T - rsSum g V T'|
      = |(rsSum g V T - rsSum g V R) - (rsSum g V T' - rsSum g V R)| := by ring_nf
    _ ≤ |rsSum g V T - rsSum g V R| + |rsSum g V T' - rsSum g V R| := abs_sub _ _
    _ ≤ ε := by linarith

/-- Continuity within `[a, b]` gives both one-sided continuities. -/
private theorem continuousWithinAt_oneSided {F : ℝ → ℝ} {x : ℝ}
    (hF : ContinuousWithinAt F (Icc a b) x) :
    ContinuousWithinAt F (Icc a b ∩ Ici x) x ∧ ContinuousWithinAt F (Icc a b ∩ Iic x) x :=
  ⟨hF.mono inter_subset_left, hF.mono inter_subset_left⟩

/-- **Existence against a monotone integrator.** Let `g` have a right limit at every point of
`[a, b)` and a left limit at every point of `(a, b]` (`g` is regulated), let `V` be monotone on
`[a, b]`, and suppose that at every point of `[a, b]` at least one of `g`, `V` is continuous
within `[a, b]`. Then `∫ₐᵇ g dV` exists: the special case of
`rsIntegrable_of_regulated_of_monotoneOn_oneSided` in which the same function is continuous on both
sides. -/
theorem rsIntegrable_of_regulated_of_monotoneOn {g V : ℝ → ℝ} (hab : a ≤ b)
    (hgR : ∀ x ∈ Ico a b, ∃ l, Tendsto g (𝓝[>] x) (𝓝 l))
    (hgL : ∀ x ∈ Ioc a b, ∃ l, Tendsto g (𝓝[<] x) (𝓝 l))
    (hV : MonotoneOn V (Icc a b))
    (hcont : ∀ x ∈ Icc a b,
      ContinuousWithinAt g (Icc a b) x ∨ ContinuousWithinAt V (Icc a b) x) :
    RSIntegrable g V a b :=
  rsIntegrable_of_regulated_of_monotoneOn_oneSided hab hgR hgL hV
    (fun x hx => (hcont x hx).imp (fun h => (continuousWithinAt_oneSided h).1)
      (fun h => (continuousWithinAt_oneSided h).1))
    (fun x hx => (hcont x hx).imp (fun h => (continuousWithinAt_oneSided h).2)
      (fun h => (continuousWithinAt_oneSided h).2))

/-- **Existence against a bounded-variation integrator, one-sided form.** Let `g` be regulated on
`[a, b]` and let `f` have bounded variation on `[a, b]`. If `g` and `f` have no common
discontinuity on the same side (at every point one of them is right-continuous and one of them is
left-continuous, within `[a, b]`), then `∫ₐᵇ g df` exists. -/
theorem rsIntegrable_of_regulated_of_boundedVariationOn_oneSided {g f : ℝ → ℝ} (hab : a ≤ b)
    (hgR : ∀ x ∈ Ico a b, ∃ l, Tendsto g (𝓝[>] x) (𝓝 l))
    (hgL : ∀ x ∈ Ioc a b, ∃ l, Tendsto g (𝓝[<] x) (𝓝 l))
    (hf : BoundedVariationOn f (Icc a b))
    (hright : ∀ x ∈ Icc a b,
      ContinuousWithinAt g (Icc a b ∩ Ici x) x ∨ ContinuousWithinAt f (Icc a b ∩ Ici x) x)
    (hleft : ∀ x ∈ Icc a b,
      ContinuousWithinAt g (Icc a b ∩ Iic x) x ∨ ContinuousWithinAt f (Icc a b ∩ Iic x) x) :
    RSIntegrable g f a b := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  set V := variationOnFromTo f (Icc a b) a
  have hVmono : MonotoneOn V (Icc a b) :=
    variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn ha
  have hWmono : MonotoneOn (V - f) (Icc a b) :=
    variationOnFromTo.sub_self_monotoneOn hf.locallyBoundedVariationOn ha
  have hVR : ∀ x ∈ Icc a b, ContinuousWithinAt f (Icc a b ∩ Ici x) x →
      ContinuousWithinAt V (Icc a b ∩ Ici x) x := fun x hx hfx =>
    hf.continuousWithinAt_variationOnFromTo_inter_Ici ha hx hfx
  have hVL : ∀ x ∈ Icc a b, ContinuousWithinAt f (Icc a b ∩ Iic x) x →
      ContinuousWithinAt V (Icc a b ∩ Iic x) x := fun x hx hfx =>
    hf.continuousWithinAt_variationOnFromTo_inter_Iic ha hx hfx
  obtain ⟨I₁, h₁⟩ := rsIntegrable_of_regulated_of_monotoneOn_oneSided hab hgR hgL hVmono
    (fun x hx => (hright x hx).imp id (hVR x hx)) (fun x hx => (hleft x hx).imp id (hVL x hx))
  obtain ⟨I₂, h₂⟩ := rsIntegrable_of_regulated_of_monotoneOn_oneSided hab hgR hgL hWmono
    (fun x hx => (hright x hx).imp id fun hfx => (hVR x hx hfx).sub hfx)
    (fun x hx => (hleft x hx).imp id fun hfx => (hVL x hx hfx).sub hfx)
  have h := h₁.sub_right h₂
  rw [show V - (V - f) = f by ring] at h
  exact h.rsIntegrable

/-- **Existence against a bounded-variation integrator.** Let `g` be regulated on `[a, b]`
(one-sided limits at every point) and let `f` have bounded variation on `[a, b]`. If at every
point of `[a, b]` at least one of `g`, `f` is continuous within `[a, b]`, then `∫ₐᵇ g df`
exists. -/
theorem rsIntegrable_of_regulated_of_boundedVariationOn {g f : ℝ → ℝ} (hab : a ≤ b)
    (hgR : ∀ x ∈ Ico a b, ∃ l, Tendsto g (𝓝[>] x) (𝓝 l))
    (hgL : ∀ x ∈ Ioc a b, ∃ l, Tendsto g (𝓝[<] x) (𝓝 l))
    (hf : BoundedVariationOn f (Icc a b))
    (hcont : ∀ x ∈ Icc a b,
      ContinuousWithinAt g (Icc a b) x ∨ ContinuousWithinAt f (Icc a b) x) :
    RSIntegrable g f a b :=
  rsIntegrable_of_regulated_of_boundedVariationOn_oneSided hab hgR hgL hf
    (fun x hx => (hcont x hx).imp (fun h => (continuousWithinAt_oneSided h).1)
      (fun h => (continuousWithinAt_oneSided h).1))
    (fun x hx => (hcont x hx).imp (fun h => (continuousWithinAt_oneSided h).2)
      (fun h => (continuousWithinAt_oneSided h).2))

/-- **Existence for a bounded-variation integrand against a regulated integrator, one-sided form
(Hildebrandt).** Let `f` have bounded variation on `[a, b]` and let `h` be regulated on `[a, b]`.
Suppose `f` and `h` have no common discontinuity on the same side: at every `x ∈ [a, b]`, one of
`f`, `h` is right-continuous at `x` within `[a, b] ∩ [x, ∞)`, and one of `f`, `h` is left-continuous
at `x` within `[a, b] ∩ (-∞, x]`. Then `∫ₐᵇ f dh` exists. A common jump on opposite sides is
allowed: `f = 𝟙(1, ∞)` (left-continuous) against `h = 𝟙[1, ∞)` (right-continuous) on `[0, 2]`. -/
theorem rsIntegrable_of_boundedVariationOn_of_regulated_oneSided {f h : ℝ → ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b))
    (hhR : ∀ x ∈ Ico a b, ∃ l, Tendsto h (𝓝[>] x) (𝓝 l))
    (hhL : ∀ x ∈ Ioc a b, ∃ l, Tendsto h (𝓝[<] x) (𝓝 l))
    (hright : ∀ x ∈ Icc a b,
      ContinuousWithinAt f (Icc a b ∩ Ici x) x ∨ ContinuousWithinAt h (Icc a b ∩ Ici x) x)
    (hleft : ∀ x ∈ Icc a b,
      ContinuousWithinAt f (Icc a b ∩ Iic x) x ∨ ContinuousWithinAt h (Icc a b ∩ Iic x) x) :
    RSIntegrable f h a b := by
  obtain ⟨J, hJ⟩ := rsIntegrable_of_regulated_of_boundedVariationOn_oneSided hab hhR hhL hf
    (fun x hx => (hright x hx).symm) (fun x hx => (hleft x hx).symm)
  exact hJ.integration_by_parts.rsIntegrable

/-- **Left-continuous integrand, right-continuous integrator.** If `f` has bounded variation and is
left-continuous on `[a, b]`, and `h` is regulated and right-continuous on `[a, b]`, then `∫ₐᵇ f dh`
exists, whatever jumps `f` and `h` share. -/
theorem rsIntegrable_of_boundedVariationOn_of_regulated_of_leftContinuous {f h : ℝ → ℝ}
    (hab : a ≤ b) (hf : BoundedVariationOn f (Icc a b))
    (hfL : ∀ x ∈ Icc a b, ContinuousWithinAt f (Icc a b ∩ Iic x) x)
    (hhR : ∀ x ∈ Ico a b, ∃ l, Tendsto h (𝓝[>] x) (𝓝 l))
    (hhL : ∀ x ∈ Ioc a b, ∃ l, Tendsto h (𝓝[<] x) (𝓝 l))
    (hhrc : ∀ x ∈ Icc a b, ContinuousWithinAt h (Icc a b ∩ Ici x) x) :
    RSIntegrable f h a b :=
  rsIntegrable_of_boundedVariationOn_of_regulated_oneSided hab hf hhR hhL
    (fun x hx => Or.inr (hhrc x hx)) (fun x hx => Or.inl (hfL x hx))

/-- **Existence for a bounded-variation integrand against a regulated integrator.** Let `f` have
bounded variation on `[a, b]` and let `h` be regulated on `[a, b]` (a right limit at every point of
`[a, b)`, a left limit at every point of `(a, b]`). If `f` and `h` have no common discontinuity in
`[a, b]` (at every point at least one of them is continuous within `[a, b]`), then `∫ₐᵇ f dh`
exists. -/
theorem rsIntegrable_of_boundedVariationOn_of_regulated {f h : ℝ → ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b))
    (hhR : ∀ x ∈ Ico a b, ∃ l, Tendsto h (𝓝[>] x) (𝓝 l))
    (hhL : ∀ x ∈ Ioc a b, ∃ l, Tendsto h (𝓝[<] x) (𝓝 l))
    (hcont : ∀ x ∈ Icc a b,
      ContinuousWithinAt f (Icc a b) x ∨ ContinuousWithinAt h (Icc a b) x) :
    RSIntegrable f h a b := by
  obtain ⟨J, hJ⟩ := rsIntegrable_of_regulated_of_boundedVariationOn hab hhR hhL hf
    fun x hx => (hcont x hx).symm
  exact hJ.integration_by_parts.rsIntegrable

end Integral

end MathlibExt.Analysis.Integration
