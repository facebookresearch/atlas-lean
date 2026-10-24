/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Data.EReal.Operations

/-!
# Limsup/liminf API for random-walk partial sums

For a sequence `X : ℕ → Ω → ℝ` of real random variables, write
`Sₙ(ω) = ∑_{i < n} Xᵢ(ω)` for the partial sums. This file collects the
`limsup`/`liminf` facts about `Sₙ` (as an `EReal`-valued sequence) that the
random-walk dichotomy needs:

* measurability of the partial sums and of their `limsup`/`liminf`;
* invariance of `limsup Sₙ` and `liminf Sₙ` under finitely supported
  permutations of the coordinates (on sequence space `(ℕ → ℝ)`);
* the one-step shift identities `limsup Sₙ = X₀ + limsup Sₙ ∘ shift` and
  the same for `liminf` (on sequence space);
* shift-invariance of the i.i.d. product measure `Measure.infinitePi`;
* the `0`/`1` criterion for an `EReal`-valued random variable to be
  almost surely constant, and the two conversions between
  `limsup Sₙ = ⊥` / `liminf Sₙ = ⊤` and convergence of `Sₙ` to `-∞` / `+∞`.

## Source

This formalizes the analytic preliminaries of the target "Theorem (Random
walk dichotomy)" (Lecture 23) in `v1/Atlas/TheoryOfProbability/targets.yaml`,
whose v1 formalization is
`v1/Atlas/TheoryOfProbability/code/RandomWalkDichotomyProof.lean`
(the covering lemma there is left unproved). The dichotomy itself is in
`MathlibExt.Probability.RandomWalkDichotomy`.
-/

@[expose] public section

open MeasureTheory Filter Topology ProbabilityTheory

namespace MathlibExt.Probability.RandomWalkDichotomy

/-- The `n`-th partial sum `Sₙ(ω) = ∑_{i < n} Xᵢ(ω)` of a sequence of
random variables `X`, viewed as a random walk on `ℝ`. (On rebase onto
Batch 25, this should be unified with the identical definition in
`MathlibExt.Probability.RandomWalkTailMeasurability`.) -/
noncomputable def randomWalkPartialSum {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, X i ω

/-- The `limsup` of the random-walk partial sums, as an `EReal`-valued
function. -/
noncomputable def randomWalkLimsup {Ω : Type*} (X : ℕ → Ω → ℝ) (ω : Ω) : EReal :=
  Filter.limsup (fun n => ((randomWalkPartialSum X n ω : ℝ) : EReal)) Filter.atTop

/-- The `liminf` of the random-walk partial sums, as an `EReal`-valued
function. -/
noncomputable def randomWalkLiminf {Ω : Type*} (X : ℕ → Ω → ℝ) (ω : Ω) : EReal :=
  Filter.liminf (fun n => ((randomWalkPartialSum X n ω : ℝ) : EReal)) Filter.atTop

/-- The one-step shift on sequence space: `(shiftSeq ω) i = ω (i + 1)`. -/
def shiftSeq (ω : ℕ → ℝ) : ℕ → ℝ := fun i => ω (i + 1)

/-- The coordinate process on sequence space. -/
def coordSeq (i : ℕ) (ω : ℕ → ℝ) : ℝ := ω i

theorem partialSum_succ {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    randomWalkPartialSum X (n + 1) ω =
      randomWalkPartialSum X n ω + X n ω := by
  simp only [randomWalkPartialSum, Finset.sum_range_succ]

theorem partialSum_succ' {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    randomWalkPartialSum X (n + 1) ω =
      X 0 ω + randomWalkPartialSum (fun i ω' => X (i + 1) ω') n ω := by
  have h : randomWalkPartialSum X (n + 1) ω =
      (∑ i ∈ Finset.range n, X (i + 1) ω) + X 0 ω := by
    simp only [randomWalkPartialSum, Finset.sum_range_succ']
  rw [h]
  exact add_comm _ _

theorem measurable_partialSum {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (n : ℕ) :
    Measurable (fun ω => randomWalkPartialSum X n ω) :=
  Finset.measurable_sum (Finset.range n) (fun i _ => hX i)

theorem measurable_randomWalkLimsup {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) : Measurable (randomWalkLimsup X) := by
  apply Measurable.limsup
  intro n
  exact continuous_coe_real_ereal.measurable.comp (measurable_partialSum X hX n)

theorem measurable_randomWalkLiminf {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) : Measurable (randomWalkLiminf X) := by
  apply Measurable.liminf
  intro n
  exact continuous_coe_real_ereal.measurable.comp (measurable_partialSum X hX n)

/-- Dropping the first term does not change the `limsup` of a sequence. -/
theorem limsup_succ_eq {u : ℕ → EReal} :
    Filter.limsup (fun n => u (n + 1)) Filter.atTop = Filter.limsup u Filter.atTop := by
  rw [Filter.limsup_eq, Filter.limsup_eq]
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    rw [Filter.eventually_atTop] at h ⊢
    obtain ⟨N, hN⟩ := h
    refine ⟨N + 1, fun n hn => ?_⟩
    have h' := hN (n - 1) (by omega)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h'
  · intro h
    rw [Filter.eventually_atTop] at h ⊢
    obtain ⟨N, hN⟩ := h
    exact ⟨N, fun n hn => hN (n + 1) (by omega)⟩

/-- Dropping the first term does not change the `liminf` of a sequence. -/
theorem liminf_succ_eq {u : ℕ → EReal} :
    Filter.liminf (fun n => u (n + 1)) Filter.atTop = Filter.liminf u Filter.atTop := by
  rw [Filter.liminf_eq, Filter.liminf_eq]
  congr 1
  ext a
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro h
    rw [Filter.eventually_atTop] at h ⊢
    obtain ⟨N, hN⟩ := h
    refine ⟨N + 1, fun n hn => ?_⟩
    have h' := hN (n - 1) (by omega)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at h'
  · intro h
    rw [Filter.eventually_atTop] at h ⊢
    obtain ⟨N, hN⟩ := h
    exact ⟨N, fun n hn => hN (n + 1) (by omega)⟩

/-- Adding a finite constant commutes with `limsup` for real sequences,
viewed in `EReal`. -/
theorem limsup_add_const (c : ℝ) (u : ℕ → ℝ) :
    Filter.limsup (fun n => ((c + u n : ℝ) : EReal)) Filter.atTop =
      (c : EReal) + Filter.limsup (fun n => ((u n : ℝ) : EReal)) Filter.atTop := by
  have hc_ne_bot : (c : EReal) ≠ ⊥ := EReal.coe_ne_bot c
  have hc_ne_top : (c : EReal) ≠ ⊤ := EReal.coe_ne_top c
  rw [Filter.limsup_eq, Filter.limsup_eq]
  have hset : {a : EReal | ∀ᶠ n in Filter.atTop, ((c + u n : ℝ) : EReal) ≤ a} =
      (fun a => (c : EReal) + a) ''
        {a : EReal | ∀ᶠ n in Filter.atTop, ((u n : ℝ) : EReal) ≤ a} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro h
      refine ⟨a - (c : EReal), ?_, by rw [add_comm, EReal.sub_add_cancel]⟩
      have h' : ∀ᶠ n in Filter.atTop, ((u n : ℝ) : EReal) ≤ a - (c : EReal) := by
        filter_upwards [h] with n hn
        rw [EReal.coe_add] at hn
        rw [add_comm (c : EReal) ((u n : ℝ) : EReal)] at hn
        exact (EReal.le_sub_iff_add_le (Or.inl hc_ne_bot) (Or.inl hc_ne_top)).mpr hn
      exact h'
    · rintro ⟨b, hb, rfl⟩
      filter_upwards [hb] with n hn
      rw [EReal.coe_add]
      exact add_le_add_right hn _
  rw [hset]
  set B : Set EReal := {a : EReal | ∀ᶠ n in Filter.atTop, ((u n : ℝ) : EReal) ≤ a}
    with hB
  set I : Set EReal := (fun a => (c : EReal) + a) '' B with hI
  have hB_ne : B.Nonempty :=
    ⟨⊤, Filter.Eventually.of_forall fun n => (le_top : ((u n : ℝ) : EReal) ≤ ⊤)⟩
  have hB_bdd : BddBelow B := ⟨⊥, fun _ _ => bot_le⟩
  have hI_ne : I.Nonempty := ⟨(c : EReal) + ⊤, ⟨⊤, Filter.Eventually.of_forall fun n => (le_top : ((u n : ℝ) : EReal) ≤ ⊤), rfl⟩⟩
  have hI_bdd : BddBelow I := ⟨⊥, fun _ _ => bot_le⟩
  apply le_antisymm
  · -- `sInf I ≤ c + sInf B`, via `sInf I - c ≤ sInf B`.
    have h1 : sInf I - (c : EReal) ≤ sInf B := by
      apply le_csInf hB_ne
      intro b hb
      rw [EReal.sub_le_iff_le_add (Or.inl hc_ne_bot) (Or.inl hc_ne_top)]
      have h2 : sInf I ≤ (c : EReal) + b := csInf_le hI_bdd ⟨b, hb, rfl⟩
      rwa [add_comm] at h2
    calc sInf I = (sInf I - (c : EReal)) + (c : EReal) := (EReal.sub_add_cancel).symm
      _ ≤ sInf B + (c : EReal) := add_le_add_left h1 _
      _ = (c : EReal) + sInf B := add_comm _ _
  · -- `c + sInf B ≤ sInf I`: `c + sInf B` is a lower bound of `I`.
    apply le_csInf hI_ne
    rintro _ ⟨b, hb, rfl⟩
    have h2 : sInf B ≤ b := csInf_le hB_bdd hb
    exact add_le_add_right h2 _

/-- Adding a finite constant commutes with `liminf` for real sequences,
viewed in `EReal`. -/
theorem liminf_add_const (c : ℝ) (u : ℕ → ℝ) :
    Filter.liminf (fun n => ((c + u n : ℝ) : EReal)) Filter.atTop =
      (c : EReal) + Filter.liminf (fun n => ((u n : ℝ) : EReal)) Filter.atTop := by
  have hc_ne_bot : (c : EReal) ≠ ⊥ := EReal.coe_ne_bot c
  have hc_ne_top : (c : EReal) ≠ ⊤ := EReal.coe_ne_top c
  rw [Filter.liminf_eq, Filter.liminf_eq]
  have hset : {a : EReal | ∀ᶠ n in Filter.atTop, a ≤ ((c + u n : ℝ) : EReal)} =
      (fun a => (c : EReal) + a) ''
        {a : EReal | ∀ᶠ n in Filter.atTop, a ≤ ((u n : ℝ) : EReal)} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro h
      refine ⟨a - (c : EReal), ?_, by rw [add_comm, EReal.sub_add_cancel]⟩
      have h' : ∀ᶠ n in Filter.atTop, a - (c : EReal) ≤ ((u n : ℝ) : EReal) := by
        filter_upwards [h] with n hn
        rw [EReal.coe_add] at hn
        rw [add_comm (c : EReal) ((u n : ℝ) : EReal)] at hn
        exact (EReal.sub_le_iff_le_add (Or.inl hc_ne_bot) (Or.inl hc_ne_top)).mpr hn
      exact h'
    · rintro ⟨b, hb, rfl⟩
      filter_upwards [hb] with n hn
      rw [EReal.coe_add]
      exact add_le_add_right hn _
  rw [hset]
  set B : Set EReal := {a : EReal | ∀ᶠ n in Filter.atTop, a ≤ ((u n : ℝ) : EReal)}
    with hB
  set I : Set EReal := (fun a => (c : EReal) + a) '' B with hI
  have hB_ne : B.Nonempty :=
    ⟨⊥, Filter.Eventually.of_forall fun n => (bot_le : (⊥ : EReal) ≤ ((u n : ℝ) : EReal))⟩
  have hB_bdd : BddAbove B := ⟨⊤, fun _ _ => le_top⟩
  have hI_ne : I.Nonempty := ⟨(c : EReal) + ⊥, ⟨⊥, Filter.Eventually.of_forall fun n => (bot_le : (⊥ : EReal) ≤ ((u n : ℝ) : EReal)), rfl⟩⟩
  have hI_bdd : BddAbove I := ⟨⊤, fun _ _ => le_top⟩
  apply le_antisymm
  · -- `sSup I ≤ c + sSup B`: every element of `I` is `≤ c + sSup B`.
    apply csSup_le hI_ne
    rintro _ ⟨b, hb, rfl⟩
    have h2 : b ≤ sSup B := le_csSup hB_bdd hb
    exact add_le_add_right h2 _
  · -- `c + sSup B ≤ sSup I`, via the upper bounds of `I`.
    rw [le_csSup_iff hI_bdd hI_ne]
    intro u hu
    -- `u - c` is an upper bound of `B`
    have hub : sSup B ≤ u - (c : EReal) := by
      apply csSup_le hB_ne
      intro b hb
      have h1 : (c : EReal) + b ≤ u := hu ⟨b, hb, rfl⟩
      rw [add_comm (c : EReal) b] at h1
      exact (EReal.le_sub_iff_add_le (Or.inl hc_ne_bot) (Or.inl hc_ne_top)).mpr h1
    have h2 : sSup B + (c : EReal) ≤ u :=
      (EReal.le_sub_iff_add_le (Or.inl hc_ne_bot) (Or.inl hc_ne_top)).mp hub
    rwa [add_comm] at h2

/-- The `limsup` of the partial sums satisfies the one-step shift identity
`limsup Sₙ = ω₀ + limsup Sₙ ∘ shift` pointwise on sequence space. -/
theorem limsup_shift (ω : ℕ → ℝ) :
    randomWalkLimsup coordSeq ω =
      (ω 0 : EReal) + randomWalkLimsup coordSeq (shiftSeq ω) := by
  have hsum : ∀ n : ℕ, randomWalkPartialSum coordSeq (n + 1) ω =
      ω 0 + randomWalkPartialSum coordSeq n (shiftSeq ω) := by
    intro n
    show (∑ i ∈ Finset.range (n + 1), coordSeq i ω) =
      ω 0 + ∑ i ∈ Finset.range n, coordSeq i (shiftSeq ω)
    rw [Finset.sum_range_succ']
    exact add_comm _ _
  have h1 : randomWalkLimsup coordSeq ω =
      Filter.limsup (fun n => ((randomWalkPartialSum coordSeq (n + 1) ω : ℝ) : EReal))
        Filter.atTop :=
    limsup_succ_eq.symm
  have h2 : (fun n => ((randomWalkPartialSum coordSeq (n + 1) ω : ℝ) : EReal)) =
      (fun n => ((ω 0 + randomWalkPartialSum coordSeq n (shiftSeq ω) : ℝ) : EReal)) := by
    funext n
    rw [hsum n]
  rw [h1, h2, limsup_add_const]
  rfl

/-- The `liminf` of the partial sums satisfies the one-step shift identity
`liminf Sₙ = ω₀ + liminf Sₙ ∘ shift` pointwise on sequence space. -/
theorem liminf_shift (ω : ℕ → ℝ) :
    randomWalkLiminf coordSeq ω =
      (ω 0 : EReal) + randomWalkLiminf coordSeq (shiftSeq ω) := by
  have hsum : ∀ n : ℕ, randomWalkPartialSum coordSeq (n + 1) ω =
      ω 0 + randomWalkPartialSum coordSeq n (shiftSeq ω) := by
    intro n
    show (∑ i ∈ Finset.range (n + 1), coordSeq i ω) =
      ω 0 + ∑ i ∈ Finset.range n, coordSeq i (shiftSeq ω)
    rw [Finset.sum_range_succ']
    exact add_comm _ _
  have h1 : randomWalkLiminf coordSeq ω =
      Filter.liminf (fun n => ((randomWalkPartialSum coordSeq (n + 1) ω : ℝ) : EReal))
        Filter.atTop :=
    liminf_succ_eq.symm
  have h2 : (fun n => ((randomWalkPartialSum coordSeq (n + 1) ω : ℝ) : EReal)) =
      (fun n => ((ω 0 + randomWalkPartialSum coordSeq n (shiftSeq ω) : ℝ) : EReal)) := by
    funext n
    rw [hsum n]
  rw [h1, h2, liminf_add_const]
  rfl

/-- A finitely supported permutation of `ℕ` that fixes all `n ≥ N` permutes
`Finset.range n` for `n ≥ N`. -/
private theorem perm_maps_range {σ : Equiv.Perm ℕ} {N n : ℕ} (hN : n ≥ N)
    (hσ : ∀ m, m ≥ N → σ m = m) (i : ℕ) (hi : i ∈ Finset.range n) :
    σ i ∈ Finset.range n := by
  simp only [Finset.mem_range] at hi ⊢
  by_cases hiN : i ≥ N
  · rw [hσ i hiN]
    exact hi
  · -- `σ i < N`: either `σ i = i < N ≤ n`, or `σ i` lies in the support,
    -- and the support is contained in `[0, N)`.
    by_cases hfix : σ i = i
    · rw [hfix]
      exact lt_of_lt_of_le (lt_of_not_ge hiN) hN
    · -- `σ i ≠ i`, so `σ i` is moved by `σ⁻¹` too in the sense that
      -- `σ⁻¹ (σ i) = i`; we show `σ i < N` by contradiction: if
      -- `σ i ≥ N` then `σ (σ i) = σ i`, so `σ` fixes `σ i`, and applying
      -- `σ⁻¹` gives `σ i = i`, contradiction.
      by_contra hcon
      push Not at hcon
      have h1 : σ (σ i) = σ i := hσ (σ i) (le_trans hN hcon)
      have h2 : σ i = i := σ.injective h1
      exact hfix h2

/-- Partial sums are invariant under finitely supported coordinate
permutations, eventually in `n`. -/
theorem partialSum_comp_perm_eq {σ : Equiv.Perm ℕ} {N : ℕ}
    (hσ : ∀ m, m ≥ N → σ m = m) {ω : ℕ → ℝ} {n : ℕ} (hn : n ≥ N) :
    randomWalkPartialSum coordSeq n (ω ∘ ⇑σ) =
      randomWalkPartialSum coordSeq n ω := by
  simp only [randomWalkPartialSum, coordSeq, Function.comp_apply]
  refine Finset.sum_bij (fun i _ => σ i) (fun i hi => perm_maps_range hn hσ i hi)
    (fun i _ j _ hij => σ.injective hij) (fun j hj => ?_) (fun i _ => rfl)
  -- surjectivity: the preimage of `j` under `σ` lies in `range n`
  refine ⟨σ.symm j, ?_, by simp⟩
  apply perm_maps_range hn _ j hj
  intro m hm
  -- `σ⁻¹` also fixes all `m ≥ N`: `σ m = m` implies `σ⁻¹ m = m`.
  have : σ m = m := hσ m hm
  calc σ.symm m = σ.symm (σ m) := by rw [this]
    _ = m := σ.symm_apply_apply m

/-- The `limsup` of the partial sums is invariant under finitely supported
coordinate permutations. -/
theorem limsup_comp_perm {σ : Equiv.Perm ℕ} (hσ : Set.Finite {n : ℕ | σ n ≠ n})
    (ω : ℕ → ℝ) :
    randomWalkLimsup coordSeq (ω ∘ ⇑σ) = randomWalkLimsup coordSeq ω := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ∈ {n : ℕ | σ n ≠ n}, n < N := by
    by_cases hempty : {n : ℕ | σ n ≠ n} = ∅
    · refine ⟨0, fun n hn => ?_⟩
      rw [hempty] at hn
      exact absurd hn (Set.notMem_empty n)
    · have hbdd : BddAbove {n : ℕ | σ n ≠ n} := hσ.bddAbove
      obtain ⟨N, hN⟩ := hbdd
      exact ⟨N + 1, fun n hn => lt_of_le_of_lt (hN hn) (Nat.lt_succ_self N)⟩
  have hfix : ∀ m, m ≥ N → σ m = m := by
    intro m hm
    by_contra hcon
    exact absurd (hN m hcon) (not_lt_of_ge hm)
  apply Filter.limsup_congr
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [partialSum_comp_perm_eq hfix hn]

/-- The `liminf` of the partial sums is invariant under finitely supported
coordinate permutations. -/
theorem liminf_comp_perm {σ : Equiv.Perm ℕ} (hσ : Set.Finite {n : ℕ | σ n ≠ n})
    (ω : ℕ → ℝ) :
    randomWalkLiminf coordSeq (ω ∘ ⇑σ) = randomWalkLiminf coordSeq ω := by
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ∈ {n : ℕ | σ n ≠ n}, n < N := by
    by_cases hempty : {n : ℕ | σ n ≠ n} = ∅
    · refine ⟨0, fun n hn => ?_⟩
      rw [hempty] at hn
      exact absurd hn (Set.notMem_empty n)
    · have hbdd : BddAbove {n : ℕ | σ n ≠ n} := hσ.bddAbove
      obtain ⟨N, hN⟩ := hbdd
      exact ⟨N + 1, fun n hn => lt_of_le_of_lt (hN hn) (Nat.lt_succ_self N)⟩
  have hfix : ∀ m, m ≥ N → σ m = m := by
    intro m hm
    by_contra hcon
    exact absurd (hN m hcon) (not_lt_of_ge hm)
  apply Filter.liminf_congr
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [partialSum_comp_perm_eq hfix hn]

/-- The i.i.d. product measure is invariant under the one-step shift. -/
theorem map_shiftSeq_infinitePi (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    (Measure.infinitePi (fun _ : ℕ => ρ)).map shiftSeq =
      Measure.infinitePi (fun _ : ℕ => ρ) := by
  apply MeasureTheory.Measure.eq_infinitePi
  intro s t ht
  have hmeas : Measurable shiftSeq :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (i + 1)
  rw [MeasureTheory.Measure.map_apply hmeas
    (MeasurableSet.pi (Finset.countable_toSet s) (fun i _ => ht i))]
  have hpre : shiftSeq ⁻¹' (Set.pi s t) =
      Set.pi (s.image (· + 1)) (fun j => if j = 0 then Set.univ else t (j - 1)) := by
    ext ω
    show (∀ i ∈ s, ω (i + 1) ∈ t i) ↔
      ∀ j ∈ s.image (· + 1), ω j ∈ (if j = 0 then Set.univ else t (j - 1))
    constructor
    · intro h j hj
      simp only [Finset.mem_image] at hj
      obtain ⟨i, hi, rfl⟩ := hj
      rw [ite_eq_right (by omega : i + 1 ≠ 0), Nat.add_sub_cancel]
      exact h i hi
    · intro h i hi
      have hi' : i + 1 ∈ s.image (· + 1) := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      have h' := h (i + 1) hi'
      change ω (i + 1) ∈ (if i + 1 = 0 then Set.univ else t (i + 1 - 1)) at h'
      rwa [ite_eq_right (by omega : i + 1 ≠ 0), Nat.add_sub_cancel] at h'
  rw [hpre, Measure.infinitePi_pi]
  · rw [Finset.prod_image]
    · refine Finset.prod_congr rfl fun i hi => ?_
      show ρ (if i + 1 = 0 then Set.univ else t (i + 1 - 1)) = ρ (t i)
      rw [ite_eq_right (by omega : i + 1 ≠ 0), Nat.add_sub_cancel]
    · intro i _ j _ hij
      dsimp only at hij
      omega
  · intro j hj
    simp only [Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    show MeasurableSet (if i + 1 = 0 then Set.univ else t (i + 1 - 1))
    rw [ite_eq_right (by omega : i + 1 ≠ 0), Nat.add_sub_cancel]
    exact ht i

/-- If every real level set of an `EReal`-valued random variable has
probability `0` or `1`, then the variable is almost surely constant. -/
theorem exists_ae_eq_const_of_forall_le_zero_or_one {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → EReal}
    (hF : Measurable F)
    (h01 : ∀ a : ℝ, μ {ω | F ω ≤ (a : EReal)} = 0 ∨ μ {ω | F ω ≤ (a : EReal)} = 1) :
    ∃ c : EReal, ∀ᵐ ω ∂μ, F ω = c := by
  classical
  -- The candidate constant is the infimum of the rationals `q` whose level
  -- set has probability `1` (plus `⊤` so the set is nonempty).
  set S : Set ℚ := {q : ℚ | μ {ω | F ω ≤ ((q : ℝ) : EReal)} = 1} with hS
  set T : Set EReal := (fun q : ℚ => ((q : ℝ) : EReal)) '' S ∪ {⊤} with hT
  refine ⟨sInf T, ?_⟩
  have hT_ne : T.Nonempty := ⟨⊤, Or.inr rfl⟩
  have hmeas_le : ∀ q : ℚ, MeasurableSet {ω | F ω ≤ ((q : ℝ) : EReal)} :=
    fun q => hF measurableSet_Iic
  -- The set where `F ≤ sInf T` has full measure: it contains the countable
  -- intersection of the full-measure level sets for `q ∈ S`.
  have hae_le : ∀ᵐ ω ∂μ, F ω ≤ sInf T := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨⋂ q ∈ S, {ω | F ω ≤ ((q : ℝ) : EReal)}, ?_, ?_⟩
    · rw [mem_ae_iff]
      have hcompl : (⋂ q ∈ S, {ω | F ω ≤ ((q : ℝ) : EReal)})ᶜ =
          ⋃ q ∈ S, {ω | F ω ≤ ((q : ℝ) : EReal)}ᶜ := by
        rw [Set.compl_iInter₂]
      rw [hcompl, measure_biUnion_null_iff (Set.to_countable S)]
      intro q hq
      have hq1 : μ {ω | F ω ≤ ((q : ℝ) : EReal)} = 1 := hq
      have hcompl := measure_compl (hmeas_le q) (μ := μ) (measure_ne_top _ _)
      rw [hq1, measure_univ] at hcompl
      simpa using hcompl
    · intro ω hω
      apply le_csInf hT_ne
      rintro _ (⟨q, hq, rfl⟩ | rfl)
      · exact Set.mem_iInter₂.mp hω q hq
      · exact le_top
  -- The set where `F < sInf T` is null: any such `ω` has `F ω ≤ q` for a
  -- rational `q` with `q < sInf T`, and every such level set is null
  -- (otherwise `q` would belong to `S`, forcing `sInf T ≤ q`).
  have hae_not_lt : ∀ᵐ ω ∂μ, ¬ F ω < sInf T := by
    rw [Filter.eventually_iff_exists_mem]
    refine ⟨{ω | F ω < sInf T}ᶜ, ?_, fun ω hω => hω⟩
    rw [mem_ae_iff, compl_compl]
    have hsub : {ω | F ω < sInf T} ⊆
        ⋃ q : ℚ, ⋃ _ : ((q : ℝ) : EReal) < sInf T,
          {ω | F ω ≤ ((q : ℝ) : EReal)} := by
      intro ω hω
      obtain ⟨q, hq1, hq2⟩ := EReal.exists_rat_btwn_of_lt hω
      exact Set.mem_iUnion₂.mpr ⟨q, hq2, le_of_lt hq1⟩
    have hnull : μ (⋃ q : ℚ, ⋃ _ : ((q : ℝ) : EReal) < sInf T,
        {ω | F ω ≤ ((q : ℝ) : EReal)}) = 0 := by
      rw [measure_iUnion_null_iff]
      intro q
      rw [measure_iUnion_null_iff]
      intro hq
      have hqS : q ∉ S := by
        intro hqS
        have hmem : ((q : ℝ) : EReal) ∈ T := Or.inl ⟨q, hqS, rfl⟩
        have hle := csInf_le ⟨⊥, fun _ _ => bot_le⟩ hmem
        exact absurd hle (not_le_of_gt hq)
      rcases h01 (q : ℝ) with h0 | h1
      · exact h0
      · exact absurd h1 fun h => hqS (by rw [hS]; exact h)
    exact measure_mono_null hsub hnull
  filter_upwards [hae_le, hae_not_lt] with ω hle hnotlt
  exact le_antisymm hle (le_of_not_gt hnotlt)

/-- `limsup Sₙ = ⊥` (in `EReal`) if and only if `Sₙ → -∞`. -/
theorem tendsto_atBot_of_limsup_eq_bot {S : ℕ → ℝ}
    (h : Filter.limsup (fun n => ((S n : ℝ) : EReal)) Filter.atTop = ⊥) :
    Tendsto S Filter.atTop Filter.atBot := by
  rw [tendsto_atBot]
  intro b
  by_contra hcon
  have hfreq : ∃ᶠ n in Filter.atTop, (b : EReal) < ((S n : ℝ) : EReal) := by
    rw [Filter.not_eventually] at hcon
    exact hcon.mono fun n hn => by
      rw [not_le] at hn
      exact_mod_cast hn
  have hle : (b : EReal) ≤ Filter.limsup (fun n => ((S n : ℝ) : EReal)) Filter.atTop := by
    rw [Filter.limsup_eq]
    have htop : (⊤ : EReal) ∈
        {a : EReal | ∀ᶠ n in Filter.atTop, ((S n : ℝ) : EReal) ≤ a} :=
      Filter.Eventually.of_forall fun n => (le_top : ((S n : ℝ) : EReal) ≤ ⊤)
    apply le_csInf ⟨⊤, htop⟩
    intro a ha
    by_contra hab
    push Not at hab
    have hfalse : ∃ᶠ n : ℕ in Filter.atTop, False := by
      apply (hfreq.and_eventually ha).mono
      intro n ⟨h1, h2⟩
      exact absurd (h1.trans_le h2) (not_lt_of_gt hab)
    exact frequently_false _ hfalse
  rw [h] at hle
  exact absurd hle (by simp)

/-- `Sₙ → -∞` if and only if `limsup Sₙ = ⊥` (in `EReal`). -/
theorem limsup_eq_bot_of_tendsto_atBot {S : ℕ → ℝ}
    (h : Tendsto S Filter.atTop Filter.atBot) :
    Filter.limsup (fun n => ((S n : ℝ) : EReal)) Filter.atTop = ⊥ := by
  apply le_antisymm _ bot_le
  have hle : ∀ b : ℝ, Filter.limsup (fun n => ((S n : ℝ) : EReal)) Filter.atTop ≤
      (b : EReal) := by
    intro b
    have hev : ∀ᶠ n in Filter.atTop, ((S n : ℝ) : EReal) ≤ (b : EReal) := by
      have h' := (tendsto_atBot.mp h) b
      filter_upwards [h'] with n hn
      exact_mod_cast hn
    rw [Filter.limsup_eq]
    exact sInf_le hev
  have hinf : Filter.limsup (fun n => ((S n : ℝ) : EReal)) Filter.atTop ≤
      ⨅ b : ℝ, (b : EReal) := le_iInf hle
  have hbot : (⨅ b : ℝ, (b : EReal)) = ⊥ := by
    by_contra hne
    have hne_top : (⨅ b : ℝ, (b : EReal)) ≠ ⊤ := by
      intro htop
      have hle0 := iInf_le (fun b : ℝ => (b : EReal)) (0 : ℝ)
      rw [htop] at hle0
      exact absurd hle0 (by simp)
    have hxr : (((⨅ b : ℝ, (b : EReal)).toReal : ℝ) : EReal) = ⨅ b : ℝ, (b : EReal) :=
      EReal.coe_toReal hne_top hne
    have hle1 : (⨅ b : ℝ, (b : EReal)) ≤
        (((⨅ b : ℝ, (b : EReal)).toReal - 1 : ℝ) : EReal) := iInf_le _ _
    rw [← hxr, EReal.coe_le_coe_iff] at hle1
    simp only [EReal.toReal_coe] at hle1
    exact absurd hle1 (by linarith)
  rw [hbot] at hinf
  exact hinf

/-- `liminf Sₙ = ⊤` (in `EReal`) if and only if `Sₙ → +∞`. -/
theorem tendsto_atTop_of_liminf_eq_top {S : ℕ → ℝ}
    (h : Filter.liminf (fun n => ((S n : ℝ) : EReal)) Filter.atTop = ⊤) :
    Tendsto S Filter.atTop Filter.atTop := by
  rw [tendsto_atTop]
  intro b
  by_contra hcon
  have hfreq : ∃ᶠ n in Filter.atTop, ((S n : ℝ) : EReal) < (b : EReal) := by
    rw [Filter.not_eventually] at hcon
    exact hcon.mono fun n hn => by
      rw [not_le] at hn
      exact_mod_cast hn
  have hge : Filter.liminf (fun n => ((S n : ℝ) : EReal)) Filter.atTop ≤ (b : EReal) := by
    rw [Filter.liminf_eq]
    have hbot : (⊥ : EReal) ∈
        {a : EReal | ∀ᶠ n in Filter.atTop, a ≤ ((S n : ℝ) : EReal)} :=
      Filter.Eventually.of_forall fun n => (bot_le : (⊥ : EReal) ≤ ((S n : ℝ) : EReal))
    apply csSup_le ⟨⊥, hbot⟩
    intro a ha
    by_contra hab
    push Not at hab
    have hfalse : ∃ᶠ n : ℕ in Filter.atTop, False := by
      apply (hfreq.and_eventually ha).mono
      intro n ⟨h1, h2⟩
      exact absurd (h2.trans_lt h1) (not_lt_of_gt hab)
    exact frequently_false _ hfalse
  rw [h] at hge
  exact absurd hge (by simp)

/-- `Sₙ → +∞` if and only if `liminf Sₙ = ⊤` (in `EReal`). -/
theorem liminf_eq_top_of_tendsto_atTop {S : ℕ → ℝ}
    (h : Tendsto S Filter.atTop Filter.atTop) :
    Filter.liminf (fun n => ((S n : ℝ) : EReal)) Filter.atTop = ⊤ := by
  apply le_antisymm le_top
  have hge : ∀ b : ℝ, (b : EReal) ≤
      Filter.liminf (fun n => ((S n : ℝ) : EReal)) Filter.atTop := by
    intro b
    have hev : ∀ᶠ n in Filter.atTop, (b : EReal) ≤ ((S n : ℝ) : EReal) := by
      have h' := (tendsto_atTop.mp h) b
      filter_upwards [h'] with n hn
      exact_mod_cast hn
    rw [Filter.liminf_eq]
    exact le_csSup ⟨⊤, fun _ _ => le_top⟩ hev
  have hsup : ⨆ b : ℝ, (b : EReal) ≤
      Filter.liminf (fun n => ((S n : ℝ) : EReal)) Filter.atTop := iSup_le hge
  have htop : (⨆ b : ℝ, (b : EReal)) = ⊤ := by
    by_contra hne
    have hne_bot : (⨆ b : ℝ, (b : EReal)) ≠ ⊥ := by
      intro hbot
      have hle0 := le_iSup (fun b : ℝ => (b : EReal)) (0 : ℝ)
      rw [hbot] at hle0
      exact absurd hle0 (by simp)
    have hxr : (((⨆ b : ℝ, (b : EReal)).toReal : ℝ) : EReal) = ⨆ b : ℝ, (b : EReal) :=
      EReal.coe_toReal hne hne_bot
    have hle1 : (((⨆ b : ℝ, (b : EReal)).toReal + 1 : ℝ) : EReal) ≤
        ⨆ b : ℝ, (b : EReal) := le_iSup _ _
    rw [← hxr, EReal.coe_le_coe_iff] at hle1
    simp only [EReal.toReal_coe] at hle1
    exact absurd hle1 (by linarith)
  rw [htop] at hsup
  exact hsup

/-- The event that the coordinate random walk drifts to `+∞` is
measurable. -/
theorem measurableSet_coord_driftsToTop :
    MeasurableSet {ω : ℕ → ℝ |
      Tendsto (fun n => randomWalkPartialSum coordSeq n ω) Filter.atTop Filter.atTop} :=
  measurableSet_tendsto Filter.atTop (fun n =>
    measurable_partialSum coordSeq (fun i => measurable_pi_apply i) n)

/-- The event that the coordinate random walk drifts to `-∞` is
measurable. -/
theorem measurableSet_coord_driftsToBot :
    MeasurableSet {ω : ℕ → ℝ |
      Tendsto (fun n => randomWalkPartialSum coordSeq n ω) Filter.atTop Filter.atBot} :=
  measurableSet_tendsto Filter.atBot (fun n =>
    measurable_partialSum coordSeq (fun i => measurable_pi_apply i) n)

/-- The event that the coordinate random walk oscillates is measurable. -/
theorem measurableSet_coord_oscillates :
    MeasurableSet {ω : ℕ → ℝ |
      randomWalkLimsup coordSeq ω = ⊤ ∧ randomWalkLiminf coordSeq ω = ⊥} := by
  apply MeasurableSet.inter
  · exact (measurable_randomWalkLimsup coordSeq (fun i => measurable_pi_apply i))
      (measurableSet_singleton ⊤)
  · exact (measurable_randomWalkLiminf coordSeq (fun i => measurable_pi_apply i))
      (measurableSet_singleton ⊥)

/-- The event that every coordinate vanishes is measurable. -/
theorem measurableSet_coord_forall_eq_zero :
    MeasurableSet {ω : ℕ → ℝ | ∀ i, ω i = 0} := by
  have : {ω : ℕ → ℝ | ∀ i, ω i = 0} = ⋂ i, (fun ω : ℕ → ℝ => ω i) ⁻¹' {0} := by
    ext ω
    simp
  rw [this]
  exact MeasurableSet.iInter fun i => measurable_pi_apply i (measurableSet_singleton 0)

/-- If every coordinate vanishes almost surely, the random walk converges
to the finite limit `0`. -/
theorem convergesFinite_of_ae_forall_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} (h : ∀ᵐ ω ∂μ, ∀ i, X i ω = 0) :
    ∀ᵐ ω ∂μ, ∃ l : ℝ, Tendsto (fun n => randomWalkPartialSum X n ω) Filter.atTop
      (𝓝 l) := by
  filter_upwards [h] with ω hω
  refine ⟨0, ?_⟩
  have hsum : ∀ n, randomWalkPartialSum X n ω = 0 := by
    intro n
    simp only [randomWalkPartialSum]
    exact Finset.sum_eq_zero fun i _ => hω i
  simp only [hsum]
  exact tendsto_const_nhds

/-- The event that the coordinate random walk converges to a finite limit is
measurable. -/
theorem measurableSet_coord_convergesFinite :
    MeasurableSet {ω : ℕ → ℝ | ∃ l : ℝ,
      Tendsto (fun n => randomWalkPartialSum coordSeq n ω) Filter.atTop (𝓝 l)} :=
  MeasureTheory.measurableSet_exists_tendsto (fun n =>
    measurable_partialSum coordSeq (fun i => measurable_pi_apply i) n)

end MathlibExt.Probability.RandomWalkDichotomy
