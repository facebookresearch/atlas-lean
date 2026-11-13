/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Integration.RiemannPartition
public import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Calculus for the Riemann–Stieltjes integral

Additivity over adjacent intervals, integration by parts, and existence of `∫ₐᵇ f dh` for an
integrand `f` of bounded variation against a regulated integrator `h` with no common
discontinuity, for the refinement (Moore–Pollard) Riemann–Stieltjes integral.

**The integral is a hypothesis.** The integral is defined in `StieltjesRSIntegral.lean` (T125),
which is not imported here. Every result takes a predicate
`HasRS : (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop` together with the hypothesis `hRS` stating that
`HasRS f h a b I` holds exactly when for every `ε > 0` there is a partition `P` of `[a, b]` such
that every tagged partition refining `P` has Riemann–Stieltjes sum
`∑ₖ f(ξₖ) (h(xₖ₊₁) - h(xₖ))` within `ε` of `I`. This is T125's definition of
`HasRSIntegral f h a b I` with `rsSum` unfolded, so the results apply to it with
`HasRS := HasRSIntegral` and `hRS := fun _ _ _ _ _ => Iff.rfl`. Partitions, tagged partitions and
point-set refinement are the canonical ones of `MathlibExt.Analysis.Integration.RiemannPartition`.

**Regulated integrators.** A regulated function on `[a, b]` is stated by its defining property:
a right limit at every point of `[a, b)` and a left limit at every point of `(a, b]`. "No common
discontinuity" means that at every point of `[a, b]` at least one of `f`, `h` is continuous within
`[a, b]`. The integral does not exist in general when `f` and `h` jump on the same side at the same
point (T125's test file: `f = h = 𝟙[1, ∞)` on `[0, 2]`).

## Main results

* `hasRS_add_adjacent`: `∫ₐᶜ f dh = I` and `∫_c^b f dh = J` give `∫ₐᵇ f dh = I + J`.
* `exists_hasRS_left`, `exists_hasRS_right`, `exists_hasRS_split`: if `∫ₐᵇ f dh` exists and
  `a ≤ c ≤ b`, then `∫ₐᶜ f dh` and `∫_c^b f dh` exist and add up to it.
* `hasRS_integration_by_parts`: `∫ₐᵇ f dh = I` gives `∫ₐᵇ h df = f(b) h(b) - f(a) h(a) - I`.
* `exists_hasRS_of_regulated_of_monotoneOn`: `∫ₐᵇ g dV` exists for regulated `g` and monotone `V`
  without common discontinuities.
* `exists_hasRS_of_regulated_of_boundedVariationOn`: the same for `V` of bounded variation.
* `exists_hasRS_of_boundedVariationOn_of_regulated`: `∫ₐᵇ f dh` exists for `f` of bounded
  variation and regulated `h` without common discontinuities.
* Supporting results: uniqueness `eq_of_hasRS`, the Cauchy criterion `exists_hasRS_of_cauchy`, and
  linearity in the integrator `hasRS_sub_right`.

## Proof outline

Partitions are cut and glued through one private construction: a monotone sequence
`a = s₀ ≤ ⋯ ≤ s_N = b` with tags `sᵢ ≤ τᵢ ≤ sᵢ₊₁` (repetitions allowed) yields a tagged partition
with points `{sᵢ}` and the same Riemann–Stieltjes sums. Integration by parts is the termwise
identity `h(ξ)(f(t') - f(t)) + f(t)(h(ξ) - h(t)) + f(t')(h(t') - h(ξ)) = f(t')h(t') - f(t)h(t)`
applied to the interleaved sequence `t₀ ≤ ξ₀ ≤ t₁ ≤ ⋯ ≤ tₙ` tagged by the `tₖ`. For existence,
a compactness argument gives a finite set `S` off which `g` oscillates by at most `ε`; around each
point of `S` where `g` is discontinuous, `V` is continuous, and a short window there carries
little `V`-mass. The refinement estimate then gives the Cauchy criterion. The bounded-variation
case follows from the decomposition `f = V - (V - f)` with `V` the variation function, which is
continuous wherever `f` is (`BoundedVariationOn.continuousWithinAt_variationOnFromTo_iff`), and
the regulated-integrator case follows by integration by parts.

## Not covered

* The sharper one-sided condition (no common discontinuity on the same side) of Hildebrandt's
  theorem; the hypothesis here is two-sided.
* The Duhamel operator and the Ψ-CLM bridge.

## Source receipt

T. M. Apostol, *Mathematical Analysis*, 2nd ed. (1974), Chapter 7: Definition 7.1 (refinement
form), Theorem 7.4 (additivity: if two of `∫ₐᶜ`, `∫_c^b`, `∫ₐᵇ` exist, so does the third, with
sum), Theorem 7.6 (integration by parts), and Theorem 7.27 (existence for a continuous integrand
against a bounded-variation integrator) for the shape of the existence argument. Existence of the
refinement integral for regulated functions without common discontinuities: T. H. Hildebrandt,
"Definitions of Stieltjes integrals of the Riemann type", *Amer. Math. Monthly* 45 (1938),
265–278. Regulated functions are uniform limits of step functions: J. Dieudonné, *Foundations of
Modern Analysis* (1960), §7.6. Reused: Mathlib's `variationOnFromTo` (monotone decomposition and
its continuity) and `IsCompact.elim_nhds_subcover`; Atlas's `Partition`, `TaggedPartition` and
`IsRefinement`. Proved here: everything else. The private partition helpers (`ptN`, `tgN`,
`ofFinset`, `common`, `leftTag`, `exists_index_of_isRefinement`), the Cauchy criterion and
uniqueness restate T125's counterparts, because T125's file may not be imported; they can be
replaced by T125's declarations once it merges. The refinement estimate
`abs_sum_sub_le_of_isRefinement` generalizes T125's `abs_rsSum_sub_le_of_isRefinement` to
per-subinterval bounds `ωₖ` (T125's lemma takes one uniform `ω`, and the windowed bound in the
existence proof needs the per-subinterval form); on merge, generalize T125's lemma or keep this
one.
-/

@[expose] public section

namespace MathlibExt.Analysis.Integration.RSCalculus

open Finset Set Filter Topology
open MathlibExt.Analysis.Integration

/-- The Riemann–Stieltjes sum `∑ₖ f(ξₖ) (h(xₖ₊₁) - h(xₖ))` of a tagged partition `T`, written out
(this is `rsSum f h T` of `StieltjesRSIntegral.lean`, unfolded). -/
local notation "RS[" f ", " h ", " T "]" =>
  ∑ i : Fin (Partition.n (TaggedPartition.toPartition T)), f (TaggedPartition.tags T i) *
    (h (Partition.points (TaggedPartition.toPartition T) (Fin.succ i)) -
      h (Partition.points (TaggedPartition.toPartition T) (Fin.castSucc i)))

/-! ### `ℕ`-indexed points and tags -/

section Partitions

variable {a b c : ℝ}

/-- The points of a partition extended to `ℕ`, constant equal to `b` past the last index. -/
private noncomputable def ptN (P : Partition a b) (i : ℕ) : ℝ :=
  if hi : i ≤ P.n then P.points ⟨i, Nat.lt_succ_of_le hi⟩ else b

/-- The tags of a tagged partition extended to `ℕ`, constant equal to `b` past the last index. -/
private noncomputable def tgN (T : TaggedPartition a b) (i : ℕ) : ℝ :=
  if hi : i < T.n then T.tags ⟨i, hi⟩ else b

private theorem ptN_zero (P : Partition a b) : ptN P 0 = a := by
  simp only [ptN, Nat.zero_le, dite_true]
  exact P.first

private theorem ptN_of_le (P : Partition a b) {i : ℕ} (hi : P.n ≤ i) : ptN P i = b := by
  unfold ptN
  split_ifs with h
  · have : i = P.n := le_antisymm h hi
    subst this
    exact P.last
  · rfl

private theorem ptN_fin (P : Partition a b) (i : Fin (P.n + 1)) : ptN P i = P.points i := by
  simp [ptN, Nat.le_of_lt_succ i.isLt]

private theorem tgN_fin (T : TaggedPartition a b) (i : Fin T.n) : tgN T i = T.tags i := by
  simp [tgN, i.isLt]

private theorem monotone_ptN (P : Partition a b) : Monotone (ptN P) := by
  intro i j hij
  unfold ptN
  split_ifs with hi hj hj
  · exact P.ordered.monotone (Fin.mk_le_mk.mpr hij)
  · have := P.ordered.monotone (Fin.le_last ⟨i, Nat.lt_succ_of_le hi⟩)
    rwa [P.last] at this
  · omega
  · rfl

private theorem ptN_lt (P : Partition a b) {i j : ℕ} (hij : i < j) (hj : j ≤ P.n) :
    ptN P i < ptN P j := by
  have h := P.ordered (show (⟨i, by omega⟩ : Fin (P.n + 1)) < ⟨j, by omega⟩ from
    Fin.mk_lt_mk.mpr hij)
  rw [← ptN_fin, ← ptN_fin] at h
  exact h

private theorem ptN_mem_Icc (P : Partition a b) (i : ℕ) : ptN P i ∈ Icc a b := by
  refine ⟨?_, ?_⟩
  · calc a = ptN P 0 := (ptN_zero P).symm
      _ ≤ ptN P i := monotone_ptN P (Nat.zero_le i)
  · calc ptN P i ≤ ptN P (max i P.n) := monotone_ptN P (le_max_left _ _)
      _ = b := ptN_of_le P (le_max_right _ _)

private theorem tgN_mem (T : TaggedPartition a b) {i : ℕ} (hi : i < T.n) :
    ptN T.toPartition i ≤ tgN T i ∧ tgN T i ≤ ptN T.toPartition (i + 1) := by
  have h := T.tag_mem ⟨i, hi⟩
  have h1 := ptN_fin T.toPartition (⟨i, hi⟩ : Fin T.n).castSucc
  have h2 := ptN_fin T.toPartition (⟨i, hi⟩ : Fin T.n).succ
  simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
  rw [h1, h2, tgN_fin T ⟨i, hi⟩]
  exact h

private theorem tgN_mem_Icc (T : TaggedPartition a b) {i : ℕ} (hi : i < T.n) :
    tgN T i ∈ Icc a b :=
  ⟨(ptN_mem_Icc _ i).1.trans (tgN_mem T hi).1, (tgN_mem T hi).2.trans (ptN_mem_Icc _ _).2⟩

/-- The Riemann–Stieltjes sum of a tagged partition, in `ℕ`-indexed form. -/
private theorem sum_eq_sum_range (f h : ℝ → ℝ) (T : TaggedPartition a b) :
    ∑ i : Fin T.n, f (T.tags i) * (h (T.points i.succ) - h (T.points i.castSucc)) =
      ∑ i ∈ range T.n, f (tgN T i) * (h (ptN T.toPartition (i + 1)) - h (ptN T.toPartition i)) := by
  rw [← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun i _ => ?_
  have h1 := ptN_fin T.toPartition i.castSucc
  have h2 := ptN_fin T.toPartition i.succ
  simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
  rw [tgN_fin, h1, h2]

private theorem mem_pointSet_iff (P : Partition a b) {x : ℝ} :
    x ∈ P.pointSet ↔ ∃ i ≤ P.n, ptN P i = x := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, Nat.le_of_lt_succ i.isLt, ptN_fin P i⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, (ptN_fin P ⟨i, Nat.lt_succ_of_le hi⟩).symm⟩

private theorem mem_Icc_of_mem_pointSet (P : Partition a b) {x : ℝ} (hx : x ∈ P.pointSet) :
    x ∈ Icc a b := by
  obtain ⟨i, -, rfl⟩ := (mem_pointSet_iff P).mp hx
  exact ptN_mem_Icc P i

/-- No point of a partition lies strictly inside one of its subintervals. -/
private theorem le_or_ge_of_mem_pointSet (P : Partition a b) {k : ℕ} {x : ℝ}
    (hx : x ∈ P.pointSet) : x ≤ ptN P k ∨ ptN P (k + 1) ≤ x := by
  obtain ⟨i, -, rfl⟩ := (mem_pointSet_iff P).mp hx
  rcases le_or_gt i k with hik | hik
  · exact Or.inl (monotone_ptN P hik)
  · exact Or.inr (monotone_ptN P hik)

/-! ### Partition constructions -/

/-- The partition of `[a, b]` whose points are the elements of a finite set `S ⊆ [a, b]`
containing `a` and `b`. -/
private noncomputable def ofFinset (S : Finset ℝ) (hS : ∀ x ∈ S, x ∈ Icc a b) (ha : a ∈ S)
    (hb : b ∈ S) : Partition a b where
  n := S.card - 1
  points := S.orderEmbOfFin (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨a, ha⟩)).symm
  ordered := (S.orderEmbOfFin _).strictMono
  first := by
    have hpos : 0 < S.card - 1 + 1 := Nat.succ_pos _
    rw [show (0 : Fin (S.card - 1 + 1)) = ⟨0, hpos⟩ from rfl, Finset.orderEmbOfFin_zero _ hpos]
    exact le_antisymm (Finset.min'_le S a ha) (Finset.le_min' _ _ _ fun x hx => (hS x hx).1)
  last := by
    have hpos : 0 < S.card - 1 + 1 := Nat.succ_pos _
    rw [show Fin.last (S.card - 1) = ⟨S.card - 1 + 1 - 1, by omega⟩ from Fin.ext (by simp),
      Finset.orderEmbOfFin_last _ hpos]
    exact le_antisymm (Finset.max'_le _ _ _ fun x hx => (hS x hx).2) (Finset.le_max' S b hb)

private theorem pointSet_ofFinset (S : Finset ℝ) (hS : ∀ x ∈ S, x ∈ Icc a b) (ha : a ∈ S)
    (hb : b ∈ S) : (ofFinset S hS ha hb).pointSet = S := by
  simp only [Partition.pointSet, ofFinset]
  exact Finset.range_orderEmbOfFin _ _

/-- The common refinement of two partitions: the union of their points. -/
private noncomputable def common (P Q : Partition a b) : Partition a b :=
  ofFinset (Finset.image P.points univ ∪ Finset.image Q.points univ)
    (by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx <;>
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact mem_Icc_of_mem_pointSet _ ⟨i, rfl⟩)
    (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0, mem_univ _, P.first⟩))
    (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨Fin.last P.n, mem_univ _, P.last⟩))

private theorem common_isRefinement_left (P Q : Partition a b) : (common P Q).IsRefinement P := by
  rintro x ⟨i, rfl⟩
  rw [common, pointSet_ofFinset]
  exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (mem_univ _)))

private theorem common_isRefinement_right (P Q : Partition a b) :
    (common P Q).IsRefinement Q := by
  rintro x ⟨i, rfl⟩
  rw [common, pointSet_ofFinset]
  exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (mem_univ _)))

/-- The left-endpoint tagging of a partition. -/
private def leftTag (P : Partition a b) : TaggedPartition a b where
  toPartition := P
  tags i := P.points i.castSucc
  tag_mem _ := ⟨le_rfl, P.ordered.monotone Fin.castSucc_lt_succ.le⟩

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
    (f h : ℝ → ℝ) : RS[f, h, append T hcb τ hτ] = RS[f, h, T] + f τ * (h b - h c) := by
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
      RS[f, h, T] = ∑ i ∈ range N, f (τ i) * (h (s (i + 1)) - h (s i)) := by
  induction N with
  | zero =>
    intro b s τ h0 hN _
    have hab : a = b := h0.symm.trans hN
    subst hab
    refine ⟨trivialPart a, fun x => ?_, fun f h => by simp [trivialPart]⟩
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
      · change RS[f, h, T0] = _
        rw [hT0sum, sum_range_succ, ← heq, sub_self, mul_zero, add_zero]

/-- **Gluing.** Tagged partitions of `[a, c]` and `[c, b]` glue to a tagged partition of `[a, b]`
with the union of the points and the sum of the Riemann–Stieltjes sums. -/
private theorem exists_glue (T₁ : TaggedPartition a c) (T₂ : TaggedPartition c b) :
    ∃ T : TaggedPartition a b, (∀ x, x ∈ T.pointSet ↔ x ∈ T₁.pointSet ∨ x ∈ T₂.pointSet) ∧
      ∀ f h : ℝ → ℝ, RS[f, h, T] = RS[f, h, T₁] + RS[f, h, T₂] := by
  set n₁ := T₁.n
  set n₂ := T₂.n
  set s : ℕ → ℝ := fun i => if i ≤ n₁ then ptN T₁.toPartition i else ptN T₂.toPartition (i - n₁)
  set τ : ℕ → ℝ := fun i => if i < n₁ then tgN T₁ i else tgN T₂ (i - n₁)
  have hs₁ : ∀ i ≤ n₁, s i = ptN T₁.toPartition i := fun i hi => by simp [s, hi]
  have hs₂ : ∀ i, n₁ ≤ i → s i = ptN T₂.toPartition (i - n₁) := by
    intro i hi
    rcases hi.lt_or_eq with hi | rfl
    · simp [s, not_le.mpr hi]
    · rw [hs₁ _ le_rfl, Nat.sub_self, ptN_zero, ptN_of_le _ le_rfl]
  have hτ₁ : ∀ i < n₁, τ i = tgN T₁ i := fun i hi => by simp [τ, hi]
  have hτ₂ : ∀ i, n₁ ≤ i → τ i = tgN T₂ (i - n₁) := fun i hi => by simp [τ, not_lt.mpr hi]
  have h0 : s 0 = a := by rw [hs₁ 0 (Nat.zero_le _), ptN_zero]
  have hN : s (n₁ + n₂) = b := by
    rw [hs₂ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left, ptN_of_le _ le_rfl]
  have htag : ∀ i < n₁ + n₂, s i ≤ τ i ∧ τ i ≤ s (i + 1) := by
    intro i hi
    rcases lt_or_ge i n₁ with h | h
    · rw [hs₁ i h.le, hs₁ (i + 1) h, hτ₁ i h]
      exact tgN_mem T₁ h
    · rw [hs₂ i h, hs₂ (i + 1) (by omega), hτ₂ i h, show i + 1 - n₁ = i - n₁ + 1 by omega]
      exact tgN_mem T₂ (by omega)
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
  · rw [hTsum, sum_range_add, sum_eq_sum_range, sum_eq_sum_range]
    congr 1
    · refine sum_congr rfl fun i hi => ?_
      have hi := Finset.mem_range.mp hi
      rw [hτ₁ i hi, hs₁ i hi.le, hs₁ (i + 1) hi]
    · refine sum_congr rfl fun i _ => ?_
      rw [hτ₂ _ (Nat.le_add_right _ _), hs₂ _ (Nat.le_add_right _ _),
        hs₂ _ (by omega), Nat.add_sub_cancel_left, show n₁ + i + 1 - n₁ = i + 1 by omega]

/-- **Splitting.** A tagged partition of `[a, b]` splits at any of its points into tagged partitions
of the two subintervals. -/
private theorem exists_split (T : TaggedPartition a b) {m : ℕ} (hm : m ≤ T.n) :
    ∃ (T₁ : TaggedPartition a (ptN T.toPartition m))
      (T₂ : TaggedPartition (ptN T.toPartition m) b),
      (∀ x, x ∈ T₁.pointSet ↔ x ∈ T.pointSet ∧ x ≤ ptN T.toPartition m) ∧
      (∀ x, x ∈ T₂.pointSet ↔ x ∈ T.pointSet ∧ ptN T.toPartition m ≤ x) ∧
      ∀ f h : ℝ → ℝ, RS[f, h, T] = RS[f, h, T₁] + RS[f, h, T₂] := by
  set p := ptN T.toPartition
  obtain ⟨T₁, h1set, h1sum⟩ := exists_of_seq m p (tgN T) (ptN_zero _) rfl
    (fun i hi => tgN_mem T (by omega))
  obtain ⟨T₂, h2set, h2sum⟩ := exists_of_seq (a := p m) (b := b) (T.n - m) (fun i => p (m + i))
    (fun i => tgN T (m + i)) (by simp) (by rw [Nat.add_sub_cancel' hm]; exact ptN_of_le _ le_rfl)
    (fun i hi => by rw [← add_assoc]; exact tgN_mem T (by omega))
  refine ⟨T₁, T₂, fun x => ?_, fun x => ?_, fun f h => ?_⟩
  · rw [h1set, mem_pointSet_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, by omega, rfl⟩, monotone_ptN _ hi⟩
    · rintro ⟨⟨i, hi, rfl⟩, hle⟩
      refine ⟨i, ?_, rfl⟩
      by_contra hmi
      exact absurd hle (not_le.mpr (ptN_lt _ (by omega) hi))
  · rw [h2set, mem_pointSet_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨m + i, by omega, rfl⟩, monotone_ptN _ (Nat.le_add_right _ _)⟩
    · rintro ⟨⟨i, hi, rfl⟩, hle⟩
      have hmi : m ≤ i := by
        by_contra hmi
        exact absurd hle (not_le.mpr (ptN_lt _ (by omega) (by omega)))
      exact ⟨i - m, by omega, by rw [Nat.add_sub_cancel' hmi]⟩
  · rw [h1sum, h2sum, sum_eq_sum_range, ← Nat.add_sub_cancel' hm, sum_range_add]
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

private theorem le_of_ptN_le (P : Partition a b) {i j : ℕ} (hi : i ≤ P.n)
    (hij : ptN P i ≤ ptN P j) : i ≤ j := by
  by_contra hlt
  exact absurd hij (not_le.mpr (ptN_lt P (by omega) hi))

/-- The positions of the points of `P` among the points of a refinement `Q`. -/
private theorem exists_index_of_isRefinement {P Q : Partition a b} (href : Q.IsRefinement P) :
    ∃ ψ : ℕ → ℕ, Monotone ψ ∧ ψ 0 = 0 ∧ ψ P.n = Q.n ∧ ∀ k, ptN Q (ψ k) = ptN P k := by
  have hex : ∀ k : ℕ, ∃ j : ℕ, j ≤ Q.n ∧ ptN Q j = ptN P k := by
    intro k
    rcases le_or_gt k P.n with hk | hk
    · obtain ⟨j, hj⟩ := href ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩
      refine ⟨j, Nat.le_of_lt_succ j.isLt, ?_⟩
      rw [ptN_fin, hj, ← ptN_fin]
    · exact ⟨Q.n, le_rfl, by rw [ptN_of_le Q le_rfl, ptN_of_le P hk.le]⟩
  choose ψ hψle hψ using hex
  refine ⟨ψ, fun k k' hkk' => le_of_ptN_le Q (hψle k) ?_, ?_, ?_, hψ⟩
  · rw [hψ, hψ]; exact monotone_ptN P hkk'
  · exact Nat.le_zero.mp (le_of_ptN_le Q (hψle 0)
      (by rw [hψ, ptN_zero, ptN_zero]))
  · refine le_antisymm (hψle _) (le_of_ptN_le Q le_rfl ?_)
    rw [hψ, ptN_of_le P le_rfl, ptN_of_le Q le_rfl]

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
private theorem abs_sum_sub_le_of_isRefinement {g V : ℝ → ℝ} (hV : MonotoneOn V (Icc a b))
    (T R : TaggedPartition a b) (href : R.toPartition.IsRefinement T.toPartition) (ω : ℕ → ℝ)
    (hω : ∀ k < T.n, ∀ x ∈ Icc (ptN T.toPartition k) (ptN T.toPartition (k + 1)),
      |g (tgN T k) - g x| ≤ ω k) :
    |RS[g, V, T] - RS[g, V, R]| ≤
      ∑ k ∈ range T.n, ω k * (V (ptN T.toPartition (k + 1)) - V (ptN T.toPartition k)) := by
  obtain ⟨ψ, hψ, hψ0, hψn, hψpt⟩ := exists_index_of_isRefinement href
  set Δ : ℕ → ℝ := fun j => V (ptN R.toPartition (j + 1)) - V (ptN R.toPartition j)
  have hΔ : ∀ j, 0 ≤ Δ j := fun j =>
    sub_nonneg.mpr (hV (ptN_mem_Icc _ _) (ptN_mem_Icc _ _) (monotone_ptN _ (Nat.le_succ j)))
  have hblock : ∀ k, V (ptN T.toPartition (k + 1)) - V (ptN T.toPartition k) =
      ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), Δ j := by
    intro k
    rw [sum_Ico_sub_eq (fun j => V (ptN R.toPartition j)) (hψ (Nat.le_succ k)), hψpt, hψpt]
  have hR : RS[g, V, R] =
      ∑ k ∈ range T.n, ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), g (tgN R j) * Δ j := by
    rw [sum_eq_sum_range, ← hψn, sum_range_eq_sum_sum_Ico _ hψ hψ0]
  have hT : RS[g, V, T] =
      ∑ k ∈ range T.n, ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), g (tgN T k) * Δ j := by
    rw [sum_eq_sum_range]
    refine sum_congr rfl fun k _ => ?_
    rw [hblock, mul_sum]
  have htag : ∀ k ∈ range T.n, ∀ j ∈ Finset.Ico (ψ k) (ψ (k + 1)),
      tgN R j ∈ Icc (ptN T.toPartition k) (ptN T.toPartition (k + 1)) := by
    intro k hk j hj
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Ico] at hj
    have hjn : j < R.n := by
      have := hψ (show k + 1 ≤ T.n by omega); rw [hψn] at this; omega
    obtain ⟨h1, h2⟩ := tgN_mem R hjn
    rw [← hψpt, ← hψpt]
    exact ⟨(monotone_ptN _ hj.1).trans h1, h2.trans (monotone_ptN _ hj.2)⟩
  rw [hT, hR, ← sum_sub_distrib]
  calc |∑ k ∈ range T.n, (∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), g (tgN T k) * Δ j -
          ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), g (tgN R j) * Δ j)|
      ≤ ∑ k ∈ range T.n, |∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), g (tgN T k) * Δ j -
          ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), g (tgN R j) * Δ j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range T.n, ∑ j ∈ Finset.Ico (ψ k) (ψ (k + 1)), ω k * Δ j := by
        refine sum_le_sum fun k hk => ?_
        rw [← sum_sub_distrib]
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j hj => ?_)
        rw [← sub_mul, abs_mul, abs_of_nonneg (hΔ j)]
        exact mul_le_mul_of_nonneg_right (hω k (Finset.mem_range.mp hk) _ (htag k hk j hj)) (hΔ j)
    _ = ∑ k ∈ range T.n, ω k * (V (ptN T.toPartition (k + 1)) - V (ptN T.toPartition k)) := by
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

/-- A function continuous within a set at a point is within `κ` of its value on a closed
neighborhood. -/
private theorem exists_radius {F : ℝ → ℝ} {s : Set ℝ} {e κ : ℝ} (hκ : 0 < κ)
    (hF : ContinuousWithinAt F s e) : ∃ ρ > 0, ∀ x ∈ s, |x - e| ≤ ρ → |F x - F e| ≤ κ := by
  obtain ⟨δ, hδ, H⟩ := Metric.continuousWithinAt_iff.mp hF κ hκ
  refine ⟨δ / 2, half_pos hδ, fun x hx hxe => ?_⟩
  have := H hx (by rw [Real.dist_eq]; linarith)
  rw [Real.dist_eq] at this
  exact this.le

end Regulated

/-! ### The integral, taken as a hypothesis -/

section Integral

variable (HasRS : (ℝ → ℝ) → (ℝ → ℝ) → ℝ → ℝ → ℝ → Prop)
  (hRS : ∀ (f h : ℝ → ℝ) (a b I : ℝ), HasRS f h a b I ↔
    ∀ ε > 0, ∃ P : Partition a b, ∀ T : TaggedPartition a b, T.toPartition.IsRefinement P →
      |RS[f, h, T] - I| < ε)
include hRS

variable {a b c : ℝ}

/-- The Riemann–Stieltjes integral is unique. -/
theorem eq_of_hasRS {f h : ℝ → ℝ} {I J : ℝ} (hI : HasRS f h a b I) (hJ : HasRS f h a b J) :
    I = J := by
  rw [hRS] at hI hJ
  refine eq_of_abs_sub_le_all fun ε hε => ?_
  obtain ⟨P, hP⟩ := hI (ε / 2) (by linarith)
  obtain ⟨Q, hQ⟩ := hJ (ε / 2) (by linarith)
  have h1 := hP (leftTag (common P Q)) (common_isRefinement_left P Q)
  have h2 := hQ (leftTag (common P Q)) (common_isRefinement_right P Q)
  calc |I - J| = |(RS[f, h, leftTag (common P Q)] - J) - (RS[f, h, leftTag (common P Q)] - I)| := by
        ring_nf
    _ ≤ |RS[f, h, leftTag (common P Q)] - J| + |RS[f, h, leftTag (common P Q)] - I| := abs_sub _ _
    _ ≤ ε := by linarith

/-- **Cauchy criterion.** If for every `ε > 0` there is a partition `P` such that any two tagged
refinements of `P` have Riemann–Stieltjes sums within `ε`, then the integral exists. -/
theorem exists_hasRS_of_cauchy {f h : ℝ → ℝ}
    (hC : ∀ ε > 0, ∃ P : Partition a b, ∀ T T' : TaggedPartition a b,
      T.toPartition.IsRefinement P → T'.toPartition.IsRefinement P →
        |RS[f, h, T] - RS[f, h, T']| ≤ ε) :
    ∃ I, HasRS f h a b I := by
  choose P hP using fun n : ℕ => hC (1 / (n + 1)) (by positivity)
  let Q : ℕ → Partition a b := fun n => Nat.rec (P 0) (fun k Qk => common Qk (P (k + 1))) n
  have hQP : ∀ n, (Q n).IsRefinement (P n) := by
    intro n
    cases n with
    | zero => exact subset_rfl
    | succ k => exact common_isRefinement_right _ _
  have hQmono : ∀ n m, n ≤ m → (Q m).IsRefinement (Q n) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact subset_rfl
    | succ m _ ih => exact Set.Subset.trans ih (common_isRefinement_left (Q m) (P (m + 1)))
  set s : ℕ → ℝ := fun n => RS[f, h, leftTag (Q n)]
  have hs : ∀ n m, n ≤ m → |s m - s n| ≤ 1 / (n + 1) := fun n m hnm =>
    hP n _ _ (Set.Subset.trans (hQP n) (hQmono n m hnm)) (hQP n)
  have hcauchy : CauchySeq s := by
    refine Metric.cauchySeq_iff'.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    exact ⟨N, fun n hn => by rw [Real.dist_eq]; exact (hs N n hn).trans_lt hN⟩
  obtain ⟨I, hI⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hsI : ∀ n, |s n - I| ≤ 1 / (n + 1) := by
    intro n
    have hlim : Tendsto (fun m => |s m - s n|) atTop (𝓝 |I - s n|) := (hI.sub_const _).abs
    rw [abs_sub_comm]
    exact le_of_tendsto hlim (eventually_atTop.mpr ⟨n, fun m hm => hs n m hm⟩)
  refine ⟨I, (hRS f h a b I).mpr fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hε)
  refine ⟨P N, fun T hT => ?_⟩
  have h1 := hP N T (leftTag (Q N)) hT (hQP N)
  have h2 := hsI N
  calc |RS[f, h, T] - I| = |(RS[f, h, T] - s N) + (s N - I)| := by ring_nf
    _ ≤ |RS[f, h, T] - s N| + |s N - I| := abs_add_le _ _
    _ < ε := by linarith

/-- Linearity in the integrator: `∫ f d(g - h) = ∫ f dg - ∫ f dh`. -/
theorem hasRS_sub_right {f g h : ℝ → ℝ} {I J : ℝ} (hg : HasRS f g a b I)
    (hh : HasRS f h a b J) : HasRS f (g - h) a b (I - J) := by
  rw [hRS] at hg hh ⊢
  intro ε hε
  obtain ⟨P, hP⟩ := hg (ε / 2) (by linarith)
  obtain ⟨Q, hQ⟩ := hh (ε / 2) (by linarith)
  refine ⟨common P Q, fun T hT => ?_⟩
  have h1 := hP T (Set.Subset.trans (common_isRefinement_left P Q) hT)
  have h2 := hQ T (Set.Subset.trans (common_isRefinement_right P Q) hT)
  have hsum : RS[f, g - h, T] = RS[f, g, T] - RS[f, h, T] := by
    simp only [Pi.sub_apply, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hsum]
  calc |RS[f, g, T] - RS[f, h, T] - (I - J)| = |(RS[f, g, T] - I) - (RS[f, h, T] - J)| := by
        ring_nf
    _ ≤ |RS[f, g, T] - I| + |RS[f, h, T] - J| := abs_sub _ _
    _ < ε := by linarith

/-! ### Additivity over adjacent intervals -/

/-- **Additivity over adjacent intervals.** If `∫ₐᶜ f dh = I` and `∫_c^b f dh = J`, then
`∫ₐᵇ f dh = I + J`. -/
theorem hasRS_add_adjacent {f h : ℝ → ℝ} {I J : ℝ} (hI : HasRS f h a c I)
    (hJ : HasRS f h c b J) : HasRS f h a b (I + J) := by
  rw [hRS] at hI hJ ⊢
  intro ε hε
  obtain ⟨P₁, hP₁⟩ := hI (ε / 2) (by linarith)
  obtain ⟨P₂, hP₂⟩ := hJ (ε / 2) (by linarith)
  obtain ⟨G, hGset, -⟩ := exists_glue (leftTag P₁) (leftTag P₂)
  refine ⟨G.toPartition, fun T hT => ?_⟩
  have hc : c ∈ T.pointSet := hT ((hGset c).mpr (Or.inr ⟨0, P₂.first⟩))
  obtain ⟨m, hm, hmc⟩ := (mem_pointSet_iff _).mp hc
  subst hmc
  obtain ⟨T₁, T₂, h1set, h2set, hsum⟩ := exists_split T hm
  have h1 := hP₁ T₁ fun x hx =>
    (h1set x).mpr ⟨hT ((hGset x).mpr (Or.inl hx)), (mem_Icc_of_mem_pointSet P₁ hx).2⟩
  have h2 := hP₂ T₂ fun x hx =>
    (h2set x).mpr ⟨hT ((hGset x).mpr (Or.inr hx)), (mem_Icc_of_mem_pointSet P₂ hx).1⟩
  rw [hsum]
  calc |RS[f, h, T₁] + RS[f, h, T₂] - (I + J)| = |(RS[f, h, T₁] - I) + (RS[f, h, T₂] - J)| := by
        ring_nf
    _ ≤ |RS[f, h, T₁] - I| + |RS[f, h, T₂] - J| := abs_add_le _ _
    _ < ε := by linarith

/-- The partition points of `P` that are `≤ c`, together with `c`: a partition of `[a, c]`. -/
private noncomputable def restrictLeft (P : Partition a b) (hac : a ≤ c) : Partition a c :=
  ofFinset (insert c ((Finset.image P.points Finset.univ).filter (· ≤ c)))
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨hac, le_rfl⟩
      · obtain ⟨hx, hxc⟩ := Finset.mem_filter.mp hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨(mem_Icc_of_mem_pointSet P ⟨i, rfl⟩).1, hxc⟩)
    (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨0, mem_univ _, P.first⟩, hac⟩))
    (Finset.mem_insert_self _ _)

/-- The partition points of `P` that are `≥ c`, together with `c`: a partition of `[c, b]`. -/
private noncomputable def restrictRight (P : Partition a b) (hcb : c ≤ b) : Partition c b :=
  ofFinset (insert c ((Finset.image P.points Finset.univ).filter (c ≤ ·)))
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨le_rfl, hcb⟩
      · obtain ⟨hx, hxc⟩ := Finset.mem_filter.mp hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨hxc, (mem_Icc_of_mem_pointSet P ⟨i, rfl⟩).2⟩)
    (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨Fin.last _, mem_univ _, P.last⟩, hcb⟩))

omit hRS in
/-- Every point of `P` is a point of `restrictLeft P` or of `restrictRight P`. -/
private theorem mem_restrict (P : Partition a b) (hac : a ≤ c) (hcb : c ≤ b) {x : ℝ}
    (hx : x ∈ P.pointSet) :
    x ∈ (restrictLeft P hac).pointSet ∨ x ∈ (restrictRight (a := a) P hcb).pointSet := by
  obtain ⟨i, rfl⟩ := hx
  rw [restrictLeft, restrictRight, pointSet_ofFinset, pointSet_ofFinset]
  rcases le_total (P.points i) c with h | h
  · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem _ (mem_univ _), h⟩)))
  · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_filter.mpr
      ⟨Finset.mem_image_of_mem _ (mem_univ _), h⟩)))

/-- **Restriction to a left subinterval.** If `∫ₐᵇ f dh` exists and `a ≤ c ≤ b`, then
`∫ₐᶜ f dh` exists. -/
theorem exists_hasRS_left {f h : ℝ → ℝ} {I : ℝ} (hI : HasRS f h a b I) (hac : a ≤ c)
    (hcb : c ≤ b) : ∃ I₁, HasRS f h a c I₁ := by
  rw [hRS] at hI
  refine exists_hasRS_of_cauchy HasRS hRS fun ε hε => ?_
  obtain ⟨P, hP⟩ := hI (ε / 2) (by linarith)
  refine ⟨restrictLeft P hac, fun T T' hT hT' => ?_⟩
  obtain ⟨G, hGset, hGsum⟩ := exists_glue T (leftTag (restrictRight (a := a) P hcb))
  obtain ⟨G', hG'set, hG'sum⟩ := exists_glue T' (leftTag (restrictRight (a := a) P hcb))
  have h1 := hP G fun x hx => by
    rcases mem_restrict P hac hcb hx with h | h
    · exact (hGset x).mpr (Or.inl (hT h))
    · exact (hGset x).mpr (Or.inr h)
  have h2 := hP G' fun x hx => by
    rcases mem_restrict P hac hcb hx with h | h
    · exact (hG'set x).mpr (Or.inl (hT' h))
    · exact (hG'set x).mpr (Or.inr h)
  rw [hGsum, hG'sum] at *
  calc |RS[f, h, T] - RS[f, h, T']|
      = |(RS[f, h, T] + RS[f, h, leftTag (restrictRight (a := a) P hcb)] - I) -
          (RS[f, h, T'] + RS[f, h, leftTag (restrictRight (a := a) P hcb)] - I)| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ ε := by linarith

/-- **Restriction to a right subinterval.** If `∫ₐᵇ f dh` exists and `a ≤ c ≤ b`, then
`∫_c^b f dh` exists. -/
theorem exists_hasRS_right {f h : ℝ → ℝ} {I : ℝ} (hI : HasRS f h a b I) (hac : a ≤ c)
    (hcb : c ≤ b) : ∃ I₂, HasRS f h c b I₂ := by
  rw [hRS] at hI
  refine exists_hasRS_of_cauchy HasRS hRS fun ε hε => ?_
  obtain ⟨P, hP⟩ := hI (ε / 2) (by linarith)
  refine ⟨restrictRight P hcb, fun T T' hT hT' => ?_⟩
  obtain ⟨G, hGset, hGsum⟩ := exists_glue (leftTag (restrictLeft (b := b) P hac)) T
  obtain ⟨G', hG'set, hG'sum⟩ := exists_glue (leftTag (restrictLeft (b := b) P hac)) T'
  have h1 := hP G fun x hx => by
    rcases mem_restrict P hac hcb hx with h | h
    · exact (hGset x).mpr (Or.inl h)
    · exact (hGset x).mpr (Or.inr (hT h))
  have h2 := hP G' fun x hx => by
    rcases mem_restrict P hac hcb hx with h | h
    · exact (hG'set x).mpr (Or.inl h)
    · exact (hG'set x).mpr (Or.inr (hT' h))
  rw [hGsum, hG'sum] at *
  calc |RS[f, h, T] - RS[f, h, T']|
      = |(RS[f, h, leftTag (restrictLeft (b := b) P hac)] + RS[f, h, T] - I) -
          (RS[f, h, leftTag (restrictLeft (b := b) P hac)] + RS[f, h, T'] - I)| := by ring_nf
    _ ≤ _ := abs_sub _ _
    _ ≤ ε := by linarith

/-- **Additivity over adjacent intervals (Apostol, Theorem 7.4).** If `∫ₐᵇ f dh = I` and
`a ≤ c ≤ b`, then both `∫ₐᶜ f dh` and `∫_c^b f dh` exist and add up to `I`. -/
theorem exists_hasRS_split {f h : ℝ → ℝ} {I : ℝ} (hI : HasRS f h a b I) (hac : a ≤ c)
    (hcb : c ≤ b) : ∃ I₁ I₂, HasRS f h a c I₁ ∧ HasRS f h c b I₂ ∧ I = I₁ + I₂ := by
  obtain ⟨I₁, h₁⟩ := exists_hasRS_left HasRS hRS hI hac hcb
  obtain ⟨I₂, h₂⟩ := exists_hasRS_right HasRS hRS hI hac hcb
  exact ⟨I₁, I₂, h₁, h₂, eq_of_hasRS HasRS hRS hI (hasRS_add_adjacent HasRS hRS h₁ h₂)⟩

/-! ### Integration by parts -/

/-- **Integration by parts (Apostol, Theorem 7.6).** If `∫ₐᵇ f dh = I`, then `∫ₐᵇ h df` exists and
equals `f(b) h(b) - f(a) h(a) - I`. -/
theorem hasRS_integration_by_parts {f h : ℝ → ℝ} {I : ℝ} (hI : HasRS f h a b I) :
    HasRS h f a b (f b * h b - f a * h a - I) := by
  rw [hRS] at hI ⊢
  intro ε hε
  obtain ⟨P, hP⟩ := hI ε hε
  refine ⟨P, fun T hT => ?_⟩
  set n := T.n
  set t := ptN T.toPartition with ht
  set ξ := tgN T with hξ
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
  have h0 : s 0 = a := by rw [show (0 : ℕ) = 2 * 0 from rfl, hse, ht, ptN_zero]
  have hN : s (2 * n) = b := by rw [hse, ht, ptN_of_le _ le_rfl]
  have htag : ∀ i < 2 * n, s i ≤ τ i ∧ τ i ≤ s (i + 1) := by
    intro i hi
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' i
    · rw [hse, hτe, hso]
      exact ⟨le_rfl, (tgN_mem T (by omega)).1⟩
    · rw [hso, hτo, hss]
      exact ⟨(tgN_mem T (by omega)).2, le_rfl⟩
  obtain ⟨T', hT'set, hT'sum⟩ := exists_of_seq (2 * n) s τ h0 hN htag
  have href : T'.toPartition.IsRefinement P := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := (mem_pointSet_iff _).mp (hT hx)
    exact (hT'set _).mpr ⟨2 * k, by omega, hse k⟩
  have key := hP T' href
  have hparts : RS[h, f, T] = f b * h b - f a * h a - RS[f, h, T'] := by
    rw [hT'sum, sum_range_two_mul, sum_eq_sum_range]
    have htel : ∑ k ∈ range n, (f (t (k + 1)) * h (t (k + 1)) - f (t k) * h (t k)) =
        f b * h b - f a * h a := by
      rw [sum_range_sub (fun k => f (t k) * h (t k)), ht, ptN_of_le _ le_rfl, ptN_zero]
    rw [← htel, eq_sub_iff_add_eq, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [hτe, hτo, hso, hse, hss]
    ring
  rw [hparts, show f b * h b - f a * h a - RS[f, h, T'] - (f b * h b - f a * h a - I) =
    -(RS[f, h, T'] - I) by ring, abs_neg]
  exact key

/-! ### Existence for regulated integrands and integrators -/

/-- **Existence against a monotone integrator.** Let `g` have a right limit at every point of
`[a, b)` and a left limit at every point of `(a, b]` (`g` is regulated), let `V` be monotone on
`[a, b]`, and suppose that at every point of `[a, b]` at least one of `g`, `V` is continuous
within `[a, b]`. Then `∫ₐᵇ g dV` exists. -/
theorem exists_hasRS_of_regulated_of_monotoneOn {g V : ℝ → ℝ} (hab : a ≤ b)
    (hgR : ∀ x ∈ Ico a b, ∃ l, Tendsto g (𝓝[>] x) (𝓝 l))
    (hgL : ∀ x ∈ Ioc a b, ∃ l, Tendsto g (𝓝[<] x) (𝓝 l))
    (hV : MonotoneOn V (Icc a b))
    (hcont : ∀ x ∈ Icc a b,
      ContinuousWithinAt g (Icc a b) x ∨ ContinuousWithinAt V (Icc a b) x) :
    ∃ I, HasRS g V a b I := by
  classical
  refine exists_hasRS_of_cauchy HasRS hRS fun ε hε => ?_
  have hVab : 0 ≤ V b - V a := sub_nonneg.mpr (hV ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  set ε₁ := ε / (8 * (V b - V a + 1)) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  obtain ⟨S, B, hSmem, haS, hbS, hB, hosc⟩ := exists_finset_of_regulated hab hgR hgL hε₁pos
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB a ⟨le_rfl, hab⟩)
  set η := ε / (8 * (B + 1) * (S.card + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hρ : ∀ e, ∃ ρ > 0,
      (ContinuousWithinAt g (Icc a b) e → ∀ x ∈ Icc a b, |x - e| ≤ ρ → |g x - g e| ≤ ε₁) ∧
      (ContinuousWithinAt V (Icc a b) e → ∀ x ∈ Icc a b, |x - e| ≤ ρ → |V x - V e| ≤ η / 2) := by
    intro e
    obtain ⟨ρ₁, hρ₁, H₁⟩ : ∃ ρ > 0, ContinuousWithinAt g (Icc a b) e →
        ∀ x ∈ Icc a b, |x - e| ≤ ρ → |g x - g e| ≤ ε₁ := by
      by_cases hc : ContinuousWithinAt g (Icc a b) e
      · obtain ⟨ρ, hρ, H⟩ := exists_radius hε₁pos hc
        exact ⟨ρ, hρ, fun _ => H⟩
      · exact ⟨1, one_pos, fun h => absurd h hc⟩
    obtain ⟨ρ₂, hρ₂, H₂⟩ : ∃ ρ > 0, ContinuousWithinAt V (Icc a b) e →
        ∀ x ∈ Icc a b, |x - e| ≤ ρ → |V x - V e| ≤ η / 2 := by
      by_cases hc : ContinuousWithinAt V (Icc a b) e
      · obtain ⟨ρ, hρ, H⟩ := exists_radius (half_pos hηpos) hc
        exact ⟨ρ, hρ, fun _ => H⟩
      · exact ⟨1, one_pos, fun h => absurd h hc⟩
    exact ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂,
      fun hc x hx hxe => H₁ hc x hx (hxe.trans (min_le_left _ _)),
      fun hc x hx hxe => H₂ hc x hx (hxe.trans (min_le_right _ _))⟩
  choose ρ hρpos hρg hρV using hρ
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
  set Q := ofFinset Qs hQsmem (Finset.mem_union_left _ (Finset.mem_union_left _ haS))
    (Finset.mem_union_left _ (Finset.mem_union_left _ hbS))
  set SV := S.filter (fun e => ¬ ContinuousWithinAt g (Icc a b) e) with hSV
  -- the clamped integrators
  set W : ℝ → ℝ → ℝ := fun e x => V (max (lo e) (min x (hi e))) with hW
  have hW_mono : ∀ e ∈ S, ∀ x y, x ≤ y → W e x ≤ W e y := by
    intro e he x y hxy
    have heI := hSmem e he
    have hlohi : lo e ≤ hi e := (hlo_le e heI).trans (hle_hi e heI)
    have hmem : ∀ z, max (lo e) (min z (hi e)) ∈ Icc a b := fun z =>
      ⟨(hlo_mem e heI).1.trans (le_max_left _ _),
        max_le (hlo_mem e heI).2 ((min_le_right _ _).trans (hhi_mem e heI).2)⟩
    exact hV (hmem x) (hmem y) (max_le_max le_rfl (min_le_min hxy le_rfl))
  have hW_eq : ∀ e ∈ S, ∀ x, lo e ≤ x → x ≤ hi e → W e x = V x := by
    intro e _ x h1 h2
    simp only [hW, min_eq_left h2, max_eq_right h1]
  have hW_b : ∀ e ∈ S, W e b = V (hi e) := by
    intro e he
    have heI := hSmem e he
    simp only [hW, min_eq_right (hhi_mem e heI).2,
      max_eq_right ((hlo_le e heI).trans (hle_hi e heI))]
  have hW_a : ∀ e ∈ S, W e a = V (lo e) := by
    intro e he
    have heI := hSmem e he
    simp only [hW, min_eq_left (hhi_mem e heI).1, max_eq_left (hlo_mem e heI).1]
  -- the main estimate
  have hmain : ∀ T : TaggedPartition a b, T.toPartition.IsRefinement Q →
      ∀ R : TaggedPartition a b, R.toPartition.IsRefinement T.toPartition →
        |RS[g, V, T] - RS[g, V, R]| ≤ ε / 2 := by
    intro T hTQ R hRT
    set t := ptN T.toPartition with ht
    have hQT : ∀ x ∈ Qs, x ∈ T.pointSet := fun x hx =>
      hTQ (by rw [pointSet_ofFinset]; exact Finset.mem_coe.mpr hx)
    have hST : ∀ e ∈ S, e ∈ T.pointSet := fun e he =>
      hQT e (Finset.mem_union_left _ (Finset.mem_union_left _ he))
    have hloT : ∀ e ∈ S, lo e ∈ T.pointSet := fun e he =>
      hQT _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he)))
    have hhiT : ∀ e ∈ S, hi e ∈ T.pointSet := fun e he =>
      hQT _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ he))
    -- each subinterval of `T` is good or lies in a window around a point of `SV`
    have hclaim : ∀ k < T.n, (∀ x ∈ Icc (t k) (t (k + 1)), |g (tgN T k) - g x| ≤ 2 * ε₁) ∨
        ∃ e ∈ SV, lo e ≤ t k ∧ t (k + 1) ≤ hi e := by
      intro k hk
      have huv : t k < t (k + 1) := ptN_lt _ (Nat.lt_succ_self k) (by omega)
      have huI := ptN_mem_Icc T.toPartition k
      have hvI := ptN_mem_Icc T.toPartition (k + 1)
      have hξ := tgN_mem T hk
      by_cases hus : t k ∈ S
      · have hhi_gt : t k < hi (t k) :=
          lt_min (huv.trans_le hvI.2) (by linarith [hρpos (t k)])
        have hv_hi : t (k + 1) ≤ hi (t k) :=
          (le_or_ge_of_mem_pointSet T.toPartition (k := k) (hhiT _ hus)).resolve_left
            (not_le.mpr hhi_gt)
        by_cases hgc : ContinuousWithinAt g (Icc a b) (t k)
        · left
          intro x hx
          have hd : ∀ y ∈ Icc (t k) (t (k + 1)), |g y - g (t k)| ≤ ε₁ := by
            intro y hy
            refine hρg _ hgc y ⟨huI.1.trans hy.1, hy.2.trans hvI.2⟩ ?_
            rw [abs_of_nonneg (by linarith [hy.1])]
            linarith [hy.2, min_le_right b (t k + ρ (t k)), hhi_dist (t k) huI]
          have h1 := hd (tgN T k) hξ
          have h2 := hd x hx
          calc |g (tgN T k) - g x| = |(g (tgN T k) - g (t k)) - (g x - g (t k))| := by ring_nf
            _ ≤ |g (tgN T k) - g (t k)| + |g x - g (t k)| := abs_sub _ _
            _ ≤ 2 * ε₁ := by linarith
        · exact Or.inr ⟨t k, Finset.mem_filter.mpr ⟨hus, hgc⟩, hlo_le _ huI, hv_hi⟩
      by_cases hvs : t (k + 1) ∈ S
      · have hlo_lt : lo (t (k + 1)) < t (k + 1) :=
          max_lt (huI.1.trans_lt huv) (by linarith [hρpos (t (k + 1))])
        have hlo_u : lo (t (k + 1)) ≤ t k :=
          (le_or_ge_of_mem_pointSet T.toPartition (k := k) (hloT _ hvs)).resolve_right
            (not_le.mpr hlo_lt)
        by_cases hgc : ContinuousWithinAt g (Icc a b) (t (k + 1))
        · left
          intro x hx
          have hd : ∀ y ∈ Icc (t k) (t (k + 1)), |g y - g (t (k + 1))| ≤ ε₁ := by
            intro y hy
            refine hρg _ hgc y ⟨huI.1.trans hy.1, hy.2.trans hvI.2⟩ ?_
            rw [abs_of_nonpos (by linarith [hy.2])]
            linarith [hy.1, le_max_right a (t (k + 1) - ρ (t (k + 1)))]
          have h1 := hd (tgN T k) hξ
          have h2 := hd x hx
          calc |g (tgN T k) - g x|
              = |(g (tgN T k) - g (t (k + 1))) - (g x - g (t (k + 1)))| := by ring_nf
            _ ≤ |g (tgN T k) - g (t (k + 1))| + |g x - g (t (k + 1))| := abs_sub _ _
            _ ≤ 2 * ε₁ := by linarith
        · exact Or.inr ⟨t (k + 1), Finset.mem_filter.mpr ⟨hvs, hgc⟩, hlo_u, hle_hi _ hvI⟩
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
        rcases le_total (tgN T k) x with h | h
        · linarith [hsub _ _ hξ hx h]
        · rw [abs_sub_comm]; linarith [hsub _ _ hx hξ h]
    set ω : ℕ → ℝ := fun k =>
      if ∀ x ∈ Icc (t k) (t (k + 1)), |g (tgN T k) - g x| ≤ 2 * ε₁ then 2 * ε₁ else 2 * B
      with hω
    have hωb : ∀ k < T.n, ∀ x ∈ Icc (t k) (t (k + 1)), |g (tgN T k) - g x| ≤ ω k := by
      intro k hk x hx
      simp only [hω]
      split_ifs with h
      · exact h x hx
      · have hxI : x ∈ Icc a b :=
          ⟨(ptN_mem_Icc _ k).1.trans hx.1, hx.2.trans (ptN_mem_Icc _ (k + 1)).2⟩
        calc |g (tgN T k) - g x| ≤ |g (tgN T k)| + |g x| := abs_sub _ _
          _ ≤ 2 * B := by linarith [hB _ (tgN_mem_Icc T hk), hB x hxI]
    have hest := abs_sum_sub_le_of_isRefinement hV T R hRT ω hωb
    have hΔ : ∀ k, 0 ≤ V (t (k + 1)) - V (t k) := fun k =>
      sub_nonneg.mpr (hV (ptN_mem_Icc _ _) (ptN_mem_Icc _ _) (monotone_ptN _ (Nat.le_succ k)))
    have hΔW : ∀ e ∈ S, ∀ k, 0 ≤ W e (t (k + 1)) - W e (t k) := fun e he k =>
      sub_nonneg.mpr (hW_mono e he _ _ (monotone_ptN _ (Nat.le_succ k)))
    have hterm : ∀ k ∈ range T.n, ω k * (V (t (k + 1)) - V (t k)) ≤
        2 * ε₁ * (V (t (k + 1)) - V (t k)) +
          2 * B * ∑ e ∈ SV, (W e (t (k + 1)) - W e (t k)) := by
      intro k hk
      have hk := Finset.mem_range.mp hk
      have hsumW : 0 ≤ ∑ e ∈ SV, (W e (t (k + 1)) - W e (t k)) :=
        sum_nonneg fun e he => hΔW e (Finset.mem_filter.mp he).1 k
      simp only [hω]
      split_ifs with h
      · nlinarith [hΔ k]
      · obtain ⟨e, he, h1, h2⟩ := (hclaim k hk).resolve_left h
        have heS := (Finset.mem_filter.mp he).1
        have hsingle : W e (t (k + 1)) - W e (t k) ≤ ∑ e ∈ SV, (W e (t (k + 1)) - W e (t k)) :=
          Finset.single_le_sum (fun e he => hΔW e (Finset.mem_filter.mp he).1 k) he
        rw [hW_eq e heS _ h1 ((monotone_ptN _ (Nat.le_succ k)).trans h2),
          hW_eq e heS _ (h1.trans (monotone_ptN _ (Nat.le_succ k))) h2] at hsingle
        nlinarith [hΔ k, hε₁pos]
    have htelV : ∑ k ∈ range T.n, (V (t (k + 1)) - V (t k)) = V b - V a := by
      rw [sum_range_sub (fun k => V (t k)), ht, ptN_of_le _ le_rfl, ptN_zero]
    have htelW : ∀ e ∈ S, ∑ k ∈ range T.n, (W e (t (k + 1)) - W e (t k)) =
        V (hi e) - V (lo e) := by
      intro e he
      rw [sum_range_sub (fun k => W e (t k)), ht, ptN_of_le _ le_rfl, ptN_zero, hW_b e he,
        hW_a e he]
    have hwin : ∀ e ∈ SV, V (hi e) - V (lo e) ≤ η := by
      intro e he
      obtain ⟨heS, hgc⟩ := Finset.mem_filter.mp he
      have heI := hSmem e heS
      have hVc := (hcont e heI).resolve_left hgc
      have h1 := hρV e hVc (hi e) (hhi_mem e heI) (hhi_dist e heI)
      have h2 := hρV e hVc (lo e) (hlo_mem e heI) (hlo_dist e heI)
      calc V (hi e) - V (lo e) = (V (hi e) - V e) - (V (lo e) - V e) := by ring
        _ ≤ |V (hi e) - V e| + |V (lo e) - V e| := by
            linarith [le_abs_self (V (hi e) - V e), neg_abs_le (V (lo e) - V e)]
        _ ≤ η := by linarith
    have hcard : (SV.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_filter_le _ _
    have hsumSV : ∑ e ∈ SV, (V (hi e) - V (lo e)) ≤ S.card * η := by
      calc ∑ e ∈ SV, (V (hi e) - V (lo e)) ≤ ∑ _e ∈ SV, η := sum_le_sum hwin
        _ = SV.card * η := by rw [sum_const, nsmul_eq_mul]
        _ ≤ S.card * η := by gcongr
    have hbound : ∑ k ∈ range T.n, ω k * (V (t (k + 1)) - V (t k)) ≤
        2 * ε₁ * (V b - V a) + 2 * B * (S.card * η) := by
      calc ∑ k ∈ range T.n, ω k * (V (t (k + 1)) - V (t k))
          ≤ ∑ k ∈ range T.n, (2 * ε₁ * (V (t (k + 1)) - V (t k)) +
              2 * B * ∑ e ∈ SV, (W e (t (k + 1)) - W e (t k))) := sum_le_sum hterm
        _ = 2 * ε₁ * ∑ k ∈ range T.n, (V (t (k + 1)) - V (t k)) +
              2 * B * ∑ e ∈ SV, ∑ k ∈ range T.n, (W e (t (k + 1)) - W e (t k)) := by
            rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_comm]
        _ = 2 * ε₁ * (V b - V a) + 2 * B * ∑ e ∈ SV, (V (hi e) - V (lo e)) := by
            rw [htelV]
            congr 2
            exact sum_congr rfl fun e he => htelW e (Finset.mem_filter.mp he).1
        _ ≤ 2 * ε₁ * (V b - V a) + 2 * B * (S.card * η) := by gcongr
    have harith1 : 2 * ε₁ * (V b - V a) ≤ ε / 4 := by
      have : ε₁ * (8 * (V b - V a + 1)) = ε := div_mul_cancel₀ _ (by positivity)
      nlinarith
    have harith2 : 2 * B * (S.card * η) ≤ ε / 4 := by
      have : η * (8 * (B + 1) * (S.card + 1)) = ε := div_mul_cancel₀ _ (by positivity)
      have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
      nlinarith [mul_nonneg hB0 hS0, mul_nonneg (mul_nonneg hB0 hS0) hηpos.le]
    linarith
  refine ⟨Q, fun T T' hT hT' => ?_⟩
  set R := leftTag (common T.toPartition T'.toPartition)
  have h1 := hmain T hT R (common_isRefinement_left _ _)
  have h2 := hmain T' hT' R (common_isRefinement_right _ _)
  calc |RS[g, V, T] - RS[g, V, T']|
      = |(RS[g, V, T] - RS[g, V, R]) - (RS[g, V, T'] - RS[g, V, R])| := by ring_nf
    _ ≤ |RS[g, V, T] - RS[g, V, R]| + |RS[g, V, T'] - RS[g, V, R]| := abs_sub _ _
    _ ≤ ε := by linarith

/-- **Existence against a bounded-variation integrator.** Let `g` be regulated on `[a, b]`
(one-sided limits at every point) and let `f` have bounded variation on `[a, b]`. If at every
point of `[a, b]` at least one of `g`, `f` is continuous within `[a, b]`, then `∫ₐᵇ g df`
exists. -/
theorem exists_hasRS_of_regulated_of_boundedVariationOn {g f : ℝ → ℝ} (hab : a ≤ b)
    (hgR : ∀ x ∈ Ico a b, ∃ l, Tendsto g (𝓝[>] x) (𝓝 l))
    (hgL : ∀ x ∈ Ioc a b, ∃ l, Tendsto g (𝓝[<] x) (𝓝 l))
    (hf : BoundedVariationOn f (Icc a b))
    (hcont : ∀ x ∈ Icc a b,
      ContinuousWithinAt g (Icc a b) x ∨ ContinuousWithinAt f (Icc a b) x) :
    ∃ I, HasRS g f a b I := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  set V := variationOnFromTo f (Icc a b) a
  have hVmono : MonotoneOn V (Icc a b) :=
    variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn ha
  have hWmono : MonotoneOn (V - f) (Icc a b) :=
    variationOnFromTo.sub_self_monotoneOn hf.locallyBoundedVariationOn ha
  have hVc : ∀ x ∈ Icc a b, ContinuousWithinAt f (Icc a b) x →
      ContinuousWithinAt V (Icc a b) x := fun x hx hfx =>
    (hf.continuousWithinAt_variationOnFromTo_iff ha hx).mpr hfx
  obtain ⟨I₁, h₁⟩ := exists_hasRS_of_regulated_of_monotoneOn HasRS hRS hab hgR hgL hVmono
    fun x hx => (hcont x hx).imp id (hVc x hx)
  obtain ⟨I₂, h₂⟩ := exists_hasRS_of_regulated_of_monotoneOn HasRS hRS hab hgR hgL hWmono
    fun x hx => (hcont x hx).imp id fun hfx => (hVc x hx hfx).sub hfx
  have h := hasRS_sub_right HasRS hRS h₁ h₂
  rw [show V - (V - f) = f by ring] at h
  exact ⟨I₁ - I₂, h⟩

/-- **Existence for a bounded-variation integrand against a regulated integrator.** Let `f` have
bounded variation on `[a, b]` and let `h` be regulated on `[a, b]` (a right limit at every point of
`[a, b)`, a left limit at every point of `(a, b]`). If `f` and `h` have no common discontinuity in
`[a, b]` (at every point at least one of them is continuous within `[a, b]`), then `∫ₐᵇ f dh`
exists. -/
theorem exists_hasRS_of_boundedVariationOn_of_regulated {f h : ℝ → ℝ} (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b))
    (hhR : ∀ x ∈ Ico a b, ∃ l, Tendsto h (𝓝[>] x) (𝓝 l))
    (hhL : ∀ x ∈ Ioc a b, ∃ l, Tendsto h (𝓝[<] x) (𝓝 l))
    (hcont : ∀ x ∈ Icc a b,
      ContinuousWithinAt f (Icc a b) x ∨ ContinuousWithinAt h (Icc a b) x) :
    ∃ I, HasRS f h a b I := by
  obtain ⟨J, hJ⟩ := exists_hasRS_of_regulated_of_boundedVariationOn HasRS hRS hab hhR hhL hf
    fun x hx => (hcont x hx).symm
  exact ⟨_, hasRS_integration_by_parts HasRS hRS hJ⟩

end Integral

end MathlibExt.Analysis.Integration.RSCalculus
