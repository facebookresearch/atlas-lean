/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import MathlibExt.Probability.MarkovMixing
public import CSLibExt.InformationRetrieval.PageRank

/-!
# Calibrated language models must hallucinate (finite core)

Finite core of Kalai and Vempala, *Calibrated Language Models Must
Hallucinate*, arXiv:2311.14648v3: coarsening and calibration
(Definition 1), the level-set miscalibration `Mis_∞` (Eq. (2)), the
adaptive partition and the miscalibration `Mis_b` (Definition 2),
Lemma 2 and Theorem 1. Lemma 2 and Theorem 1 are proved in the finite
setting: a finite set of factoids, as in the source, and a finitely
supported prior `ν = ∑ i, w i δ_{p i}` in place of the source's
`ν ∈ Δ(Δ(Y))`: draw `i` with probability `w i` and use `p i` (a
distribution over distributions on `Y`, not the mean distribution
`∑ i, w i • p i`). The module provides only the vocabulary used to state
Corollary 1: pushforward, facts, hallucinations, observed factoids
(Eq. (4)), the monofact rate (Eq. (5)), sparsity (Assumption 1) and
regularity (Definitions 3 and 4), for a finite set of documents and a
finitely supported prior over document distributions, which draws the
world `i`, with document distribution `D i`, with probability `w i`.

`Mis_b(g, p) = 0` implies that `g` is calibrated to `p`
(`isCalibratedTo_of_mis_eq_zero`), but the converse, which the source
states for every `b`, fails. A bin of the adaptive partition can contain
points where `g` takes different values, and coarsening `p` over such a
bin cannot return `g`. For example, `p = g = (1/2, 1/2, 0)` is
calibrated to itself; with `b = 2` the threshold is `t₁ = 1/2`, so the
closed first bin `[0, t₁]` is all of `Y` and `Mis₂(p, p) = 1/3`, while
`Mis_∞(p, p) = 0` (`isCalibratedTo_iff_misInf_eq_zero`). Since
`1/b ≤ min_{y ∈ supp g} g(y)` here, the same example also contradicts
the source's remark that `Mis_b = Mis_∞` for such `b`.
-/

@[expose] public section

namespace Cslib
namespace MachineLearning
namespace CalibratedHallucination

open MathlibExt.Probability.MarkovMixing (tvDist)
open Cslib.InformationRetrieval.PageRank (IsProbVec)

section Coarsening

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The `P`-coarsening of `D : Y → ℝ` (Definition 1): each point `y` gets
the average `(∑ z ∈ B, D z) / |B|` of `D` over the block `B` of `P` that
contains `y`. -/
noncomputable def coarsen (P : Finpartition (Finset.univ : Finset Y)) (D : Y → ℝ) :
    Y → ℝ :=
  fun y => (∑ z ∈ P.part y, D z) / (P.part y).card

/-- `g` is calibrated to `p` (Definition 1) when `g = coarsen P p` for some
partition `P` of `Y`. -/
def IsCalibratedTo (g p : Y → ℝ) : Prop :=
  ∃ P : Finpartition (Finset.univ : Finset Y), g = coarsen P p

/-- The level-set partition `B(g)` of `Y`: `y` and `z` lie in the same block
exactly when `g y = g z`. -/
noncomputable def levelPartition (g : Y → ℝ) :
    Finpartition (Finset.univ : Finset Y) := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker g)

/-- `‖p^{B(g)} − g‖_TV = (1/2) ∑ y, |p^{B(g)}(y) − g(y)|` for the coarsening
`p^{B(g)}` of `p` along the level sets of `g`, defined for all real functions
`g` and `p`. When `g` and `p` are probability vectors, this is the total
variation distance between `p^{B(g)}` and `g`, the source's level-set
miscalibration `Mis_∞(g, p)` (Eq. (2)). -/
noncomputable def misInf (g p : Y → ℝ) : ℝ :=
  tvDist (coarsen (levelPartition g) p) g

theorem sum_coarsen (P : Finpartition (Finset.univ : Finset Y)) (D : Y → ℝ) :
    ∑ y, coarsen P D y = ∑ y, D y := by
  have hdisj := P.disjoint
  have hre : ∀ f : Y → ℝ, ∑ y, f y = ∑ t ∈ P.parts, ∑ y ∈ t, f y := by
    intro f
    have huniv : (Finset.univ : Finset Y) = P.parts.biUnion id :=
      P.biUnion_parts.symm
    conv_lhs => rw [huniv]
    exact Finset.sum_biUnion hdisj
  rw [hre (coarsen P D), hre D]
  apply Finset.sum_congr rfl
  intro t ht
  have hcard : (t.card : ℝ) ≠ 0 := by
    have hne := P.nonempty_of_mem_parts ht
    have hpos := Finset.card_pos.mpr hne
    exact ne_of_gt (Nat.cast_pos.mpr hpos)
  have hpart : ∀ y ∈ t, P.part y = t := fun y hy => P.part_eq_of_mem ht hy
  have havg : ∑ y ∈ t, coarsen P D y = ∑ _y ∈ t, (∑ z ∈ t, D z) / t.card := by
    apply Finset.sum_congr rfl
    intro y hy
    change (∑ z ∈ P.part y, D z) / (P.part y).card = _
    rw [hpart y hy]
  rw [havg, Finset.sum_const, nsmul_eq_mul, mul_comm, div_mul_cancel₀ _ hcard]

/-- For any real functions `g` and `p` on `Y` (no normalization is needed),
`g` is calibrated to `p` exactly when `misInf g p = 0`; for probability vectors
this reads `Mis_∞(g, p) = 0`. -/
theorem isCalibratedTo_iff_misInf_eq_zero {g p : Y → ℝ} :
    IsCalibratedTo g p ↔ misInf g p = 0 := by
  classical
  constructor
  · rintro ⟨P, hP⟩
    have hconst : ∀ y z : Y, z ∈ P.part y → g z = g y := by
      intro y z hz
      have hz' : z ∈ (Finset.univ : Finset Y) := Finset.mem_univ z
      have hy : y ∈ (Finset.univ : Finset Y) := Finset.mem_univ y
      have hzy : P.part z = P.part y :=
        (P.mem_part_iff_part_eq_part hz' hy).mp hz
      rw [hP]
      change (∑ w ∈ P.part z, p w) / (P.part z).card
        = (∑ w ∈ P.part y, p w) / (P.part y).card
      rw [hzy]
    have hLmem : ∀ y z : Y, z ∈ (levelPartition g).part y ↔ g z = g y := by
      intro y z
      constructor
      · intro h
        have h2 := (Finpartition.mem_part_ofSetoid_iff_rel (a := y)
          (b := z)).mp h
        exact h2.symm
      · intro h
        have h2 : Setoid.ker g y z := h.symm
        exact (Finpartition.mem_part_ofSetoid_iff_rel (a := y)
          (b := z)).mpr h2
    have hLpart : ∀ y : Y, (levelPartition g).part y
        = Finset.univ.filter (fun z => g z = g y) := by
      intro y
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hLmem y z
    have hblock : ∀ t ∈ P.parts, ∀ y : Y,
        ∑ z ∈ t.filter (fun z => g z = g y), p z
          = (t.filter (fun z => g z = g y)).card * g y := by
      intro t ht y
      obtain ⟨w, hw⟩ := P.nonempty_of_mem_parts ht
      have hcardt : (t.card : ℝ) ≠ 0 := by
        have hpos := Finset.card_pos.mpr (P.nonempty_of_mem_parts ht)
        exact ne_of_gt (Nat.cast_pos.mpr hpos)
      have hgw : g w = (∑ z ∈ t, p z) / t.card := by
        have h1 : g w = coarsen P p w := by rw [hP]
        have h2 : P.part w = t := P.part_eq_of_mem ht hw
        rw [h1]
        change (∑ z ∈ P.part w, p z) / (P.part w).card = _
        rw [h2]
      have hsumt : ∑ z ∈ t, p z = t.card * g w := by
        rw [hgw, mul_div_cancel₀ _ hcardt]
      have hmem : ∀ z ∈ t, z ∈ P.part w := by
        intro z hz
        have h2 : P.part w = t := P.part_eq_of_mem ht hw
        rw [h2]
        exact hz
      by_cases hwy : g w = g y
      · have hsub : ∀ z ∈ t, g z = g y := by
          intro z hz
          exact (hconst w z (hmem z hz)).trans hwy
        have hfilter : t.filter (fun z => g z = g y) = t := by
          ext z
          simp only [Finset.mem_filter]
          exact ⟨fun h => h.1, fun hz => ⟨hz, hsub z hz⟩⟩
        rw [hfilter, hsumt, hwy]
      · have hsub : ∀ z ∈ t, ¬g z = g y := by
          intro z hz hcon
          exact hwy ((hconst w z (hmem z hz)).symm.trans hcon)
        have hfilter : t.filter (fun z => g z = g y) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro z
          simp only [Finset.mem_filter, not_and]
          intro hz hcon
          exact hsub z hz hcon
        rw [hfilter]
        simp
    have hmain : coarsen (levelPartition g) p = g := by
      funext y
      have hposL := Finset.card_pos.mpr
        ((levelPartition g).part_nonempty.mpr (Finset.mem_univ y))
      have hcardL : (((levelPartition g).part y).card : ℝ) ≠ 0 :=
        ne_of_gt (Nat.cast_pos.mpr hposL)
      have hdecomp : Finset.univ.filter (fun z => g z = g y)
          = P.parts.biUnion (fun t => t.filter (fun z => g z = g y)) := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_biUnion]
        constructor
        · intro hz
          obtain ⟨t, ht, hzt⟩ := P.exists_mem (Finset.mem_univ z)
          exact ⟨t, ht, hzt, hz⟩
        · rintro ⟨t, ht, hzt, hz⟩
          exact hz
      have hdisjF : Set.PairwiseDisjoint (P.parts : Set (Finset Y))
          (fun t => t.filter (fun z => g z = g y)) := by
        intro t ht u hu hne
        exact Disjoint.mono (Finset.filter_subset _ _)
          (Finset.filter_subset _ _) (P.disjoint ht hu hne)
      have hsum : ∑ z ∈ (levelPartition g).part y, p z
          = ((levelPartition g).part y).card * g y := by
        rw [hLpart y, hdecomp, Finset.sum_biUnion hdisjF]
        have hper : ∑ t ∈ P.parts, ∑ z ∈ t.filter (fun z => g z = g y), p z
            = ∑ t ∈ P.parts, (t.filter (fun z => g z = g y)).card * g y :=
          Finset.sum_congr rfl (fun t ht => hblock t ht y)
        rw [hper, ← Finset.sum_mul]
        congr 1
        conv_rhs => rw [Finset.card_eq_sum_ones, Finset.sum_biUnion hdisjF,
          Nat.cast_sum]
        exact Finset.sum_congr rfl
          (fun t _ => by rw [Finset.card_eq_sum_ones])
      change (∑ z ∈ (levelPartition g).part y, p z)
        / ((levelPartition g).part y).card = g y
      rw [hsum, mul_div_cancel_left₀ _ hcardL]
    have hfin : misInf g p = tvDist g g := by
      change tvDist (coarsen (levelPartition g) p) g = _
      rw [hmain]
    rw [hfin]
    exact MathlibExt.Probability.MarkovMixing.tvDist_self g
  · intro h0
    have hsum : ∑ y, |coarsen (levelPartition g) p y - g y| = 0 := by
      have htv : (1 / 2 : ℝ)
          * ∑ y, |coarsen (levelPartition g) p y - g y| = 0 := h0
      rcases mul_eq_zero.mp htv with h' | h'
      · norm_num at h'
      · exact h'
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => abs_nonneg _)).mp hsum
    have h01 : ∀ y, coarsen (levelPartition g) p y = g y := by
      intro y
      have hy0 := hall y (Finset.mem_univ y)
      rw [abs_eq_zero, sub_eq_zero] at hy0
      exact hy0
    exact ⟨levelPartition g, (funext h01).symm⟩

end Coarsening

section AdaptiveBins

variable {Y : Type*} [Fintype Y]

/-- The adaptive-bin threshold of Definition 2,
`t_i = sup {z ∈ [0, 1] | ∑_{y : g y ≤ z} g y ≤ i / b}` (with `i / 0 = 0`).
It is defined for every `g`, `b` and `i`; the set contains `0` and lies in
`[0, 1]`, so `0 ≤ t_i ≤ 1`. -/
noncomputable def binThreshold (g : Y → ℝ) (b i : ℕ) : ℝ :=
  sSup {z : ℝ | z ∈ Set.Icc (0 : ℝ) 1 ∧
    (∑ y ∈ Finset.univ.filter (fun y => g y ≤ z), g y) ≤ (i : ℝ) / b}

/-- `binIndex g b y = sInf {i : ℕ | g y ≤ t_{i+1}}`, defined for every `g`,
`b` and `y`: when no threshold reaches `g y` the set is empty and the value
is `0` (for instance when `g y > 1`, as every threshold is at most `1`).
When `g` is a probability vector and `1 ≤ b`, the set is nonempty, and
`binIndex g b y` is its least element `i < b`: the 0-based index of the
adaptive bin containing `y`, which is `B_[0, t_1]` for `i = 0` and
`B_(t_i, t_{i+1}]` otherwise (`binIndex_spec`). -/
noncomputable def binIndex (g : Y → ℝ) (b : ℕ) (y : Y) : ℕ :=
  sInf {i : ℕ | g y ≤ binThreshold g b (i + 1)}

theorem binThreshold_mono (g : Y → ℝ) (b : ℕ) : Monotone (binThreshold g b) := by
  intro i j hij
  have hle : (i : ℝ) / b ≤ (j : ℝ) / b := by
    by_cases hb : (b : ℝ) = 0
    · rw [hb, div_zero, div_zero]
    · have hb' : (0 : ℝ) < b := lt_of_le_of_ne (Nat.cast_nonneg b) (Ne.symm hb)
      have hij' : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
      gcongr
  change sSup {z : ℝ | z ∈ Set.Icc (0 : ℝ) 1 ∧
      (∑ y ∈ Finset.univ.filter (fun y => g y ≤ z), g y) ≤ (i : ℝ) / b}
    ≤ sSup {z : ℝ | z ∈ Set.Icc (0 : ℝ) 1 ∧
      (∑ y ∈ Finset.univ.filter (fun y => g y ≤ z), g y) ≤ (j : ℝ) / b}
  apply csSup_le_csSup
  · exact ⟨1, fun z hz => (Set.mem_Icc.mp hz.1).2⟩
  · refine ⟨0, Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩, ?_⟩
    have h0 : ∑ y ∈ Finset.univ.filter (fun y => g y ≤ 0), g y ≤ 0 := by
      apply Finset.sum_nonpos
      intro y hy
      exact (Finset.mem_filter.mp hy).2
    have hbi : (0 : ℝ) ≤ (i : ℝ) / b := by positivity
    exact le_trans h0 hbi
  · intro z hz
    exact ⟨hz.1, le_trans hz.2 hle⟩

theorem binThreshold_self {g : Y → ℝ} (hg : IsProbVec g) {b : ℕ}
    (hb : 1 ≤ b) : binThreshold g b b = 1 := by
  have hpos : 0 < b := by omega
  have hb0 : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hpos)
  have hbb : (b : ℝ) / b = 1 := div_self hb0
  have hgy1 : ∀ y, g y ≤ 1 := by
    intro y
    have h1 := Finset.single_le_sum (fun a _ => hg.1 a) (Finset.mem_univ y)
    rw [hg.2] at h1
    exact h1
  have hmem1 : (1 : ℝ) ∈ {z : ℝ | z ∈ Set.Icc (0 : ℝ) 1 ∧
      (∑ y ∈ Finset.univ.filter (fun y => g y ≤ z), g y) ≤ (b : ℝ) / b} := by
    refine ⟨Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩, ?_⟩
    have hfilter : Finset.univ.filter (fun y => g y ≤ (1 : ℝ)) = Finset.univ := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ]
      constructor
      · intro h
        trivial
      · intro _
        exact ⟨trivial, hgy1 y⟩
    simp only [hbb, hfilter, hg.2, le_refl]
  change sSup {z : ℝ | z ∈ Set.Icc (0 : ℝ) 1 ∧
      (∑ y ∈ Finset.univ.filter (fun y => g y ≤ z), g y) ≤ (b : ℝ) / b} = 1
  have hbdd : BddAbove {z : ℝ | z ∈ Set.Icc (0 : ℝ) 1 ∧
      (∑ y ∈ Finset.univ.filter (fun y => g y ≤ z), g y) ≤ (b : ℝ) / b} :=
    ⟨1, fun z hz => (Set.mem_Icc.mp hz.1).2⟩
  have hne : {z : ℝ | z ∈ Set.Icc (0 : ℝ) 1 ∧
      (∑ y ∈ Finset.univ.filter (fun y => g y ≤ z), g y)
        ≤ (b : ℝ) / b}.Nonempty :=
    ⟨1, hmem1⟩
  apply le_antisymm
  · exact csSup_le hne (fun z hz => (Set.mem_Icc.mp hz.1).2)
  · exact le_csSup hbdd hmem1

theorem binIndex_spec {g : Y → ℝ} (hg : IsProbVec g) {b : ℕ}
    (hb : 1 ≤ b) (y : Y) :
    binIndex g b y < b ∧ g y ≤ binThreshold g b (binIndex g b y + 1) ∧
      (0 < binIndex g b y → binThreshold g b (binIndex g b y) < g y) := by
  have hgy1 : g y ≤ 1 := by
    have h1 := Finset.single_le_sum (fun a _ => hg.1 a) (Finset.mem_univ y)
    rw [hg.2] at h1
    exact h1
  have htb : binThreshold g b b = 1 := binThreshold_self hg hb
  have hsub : b - 1 + 1 = b := Nat.sub_add_cancel hb
  have hmem : b - 1 ∈ {i : ℕ | g y ≤ binThreshold g b (i + 1)} := by
    change g y ≤ binThreshold g b (b - 1 + 1)
    rw [hsub, htb]
    exact hgy1
  have hne : {i : ℕ | g y ≤ binThreshold g b (i + 1)}.Nonempty := ⟨b - 1, hmem⟩
  have hbelow : BddBelow {i : ℕ | g y ≤ binThreshold g b (i + 1)} :=
    ⟨0, fun _ _ => Nat.zero_le _⟩
  have hle : binIndex g b y ≤ b - 1 := csInf_le hbelow hmem
  have h1 : binIndex g b y < b := by omega
  have h2 : g y ≤ binThreshold g b (binIndex g b y + 1) := Nat.sInf_mem hne
  refine ⟨h1, h2, fun hm => ?_⟩
  by_contra hcon
  have hge : g y ≤ binThreshold g b (binIndex g b y) := le_of_not_gt hcon
  have hsubm : binIndex g b y - 1 + 1 = binIndex g b y :=
    Nat.sub_add_cancel hm
  have hmem' : binIndex g b y - 1 ∈ {i : ℕ | g y ≤ binThreshold g b (i + 1)} := by
    change g y ≤ binThreshold g b (binIndex g b y - 1 + 1)
    rw [hsubm]
    exact hge
  have hle' : binIndex g b y ≤ binIndex g b y - 1 := csInf_le hbelow hmem'
  omega

/-- Eq. (6): for real functions `q` and `g` on `Y` with equal total masses
`∑ y, q y = ∑ y, g y`, and every `U ⊆ Y`, `q(U) − g(U) ≤ ‖q − g‖_TV`, where
`q(U) = ∑ y ∈ U, q y` and `‖q − g‖_TV = (1/2) ∑ y, |q y − g y|`. Neither mass
needs to be `1`; for probability vectors, `‖q − g‖_TV` is the total variation
distance. -/
theorem sub_le_tvDist_of_sum_eq {q g : Y → ℝ} (h : ∑ y, q y = ∑ y, g y)
    (U : Finset Y) :
    ∑ y ∈ U, q y - ∑ y ∈ U, g y ≤ tvDist q g := by
  classical
  have hsub : ∑ y ∈ U, q y - ∑ y ∈ U, g y = ∑ y ∈ U, (q y - g y) :=
    (Finset.sum_sub_distrib q g).symm
  rw [hsub]
  have htot : ∑ y ∈ Finset.univ, (q y - g y) = 0 := by
    rw [Finset.sum_sub_distrib, h, sub_self]
  have hsplit := Finset.sum_sdiff (s₁ := U) (s₂ := Finset.univ)
    (f := fun y => q y - g y) (Finset.subset_univ U)
  have hU : ∑ y ∈ U, (q y - g y) ≤ ∑ y ∈ U, |q y - g y| := by
    apply Finset.sum_le_sum
    intro y _
    exact le_abs_self _
  have hUc : -(∑ y ∈ Finset.univ \ U, (q y - g y))
      ≤ ∑ y ∈ Finset.univ \ U, |q y - g y| := by
    have h1 : ∑ y ∈ Finset.univ \ U, (-(q y - g y))
        ≤ ∑ y ∈ Finset.univ \ U, |q y - g y| := by
      apply Finset.sum_le_sum
      intro y _
      exact neg_le_abs _
    rw [Finset.sum_neg_distrib] at h1
    exact h1
  have habs := Finset.sum_sdiff (s₁ := U) (s₂ := Finset.univ)
    (f := fun y => |q y - g y|) (Finset.subset_univ U)
  have htv : tvDist q g = (1 / 2 : ℝ) * ∑ y, |q y - g y| := rfl
  rw [htv]
  linarith [hU, hUc, hsplit, habs, htot]

end AdaptiveBins

section MainTheorem

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- The partition of `Y` by the value of `binIndex g b`: `y` and `z` share a
block exactly when `binIndex g b y = binIndex g b z`. It is defined for every
`g` and `b`. When `g` is a probability vector and `1 ≤ b`, `binIndex g b y`
is the index of the source's bin containing `y` (`binIndex_spec`), so the
blocks are the nonempty bins `B_[0, t_1], B_(t_1, t_2], …, B_(t_{b-1}, t_b]`
of the adaptive partition `V_b(g)` of Definition 2. -/
noncomputable def adaptivePartition (g : Y → ℝ) (b : ℕ) :
    Finpartition (Finset.univ : Finset Y) := by
  classical
  exact Finpartition.ofSetoid (Setoid.ker (binIndex g b))

/-- `‖p^V − g‖_TV = (1/2) ∑ y, |p^V(y) − g(y)|` for the partition
`V = adaptivePartition g b`, defined for every `g`, `p` and `b`. When `g` is a
probability vector and `1 ≤ b`, the blocks of `V` are the nonempty bins of the
source's `V_b(g)`; when moreover `p` is a probability vector, this is the
source's miscalibration `Mis_b(g, p)` (Definition 2). -/
noncomputable def mis (b : ℕ) (g p : Y → ℝ) : ℝ :=
  tvDist (coarsen (adaptivePartition g b) p) g

/-- For any real functions `g` and `p` on `Y` and any `b`, if
`mis b g p = 0` then `g` is calibrated to `p`. The converse fails: a bin of
the adaptive partition can contain points where `g` takes different values,
and coarsening `p` over such a bin cannot return `g`. -/
theorem isCalibratedTo_of_mis_eq_zero {b : ℕ} {g p : Y → ℝ}
    (h : mis b g p = 0) : IsCalibratedTo g p := by
  have hsum : ∑ y, |coarsen (adaptivePartition g b) p y - g y| = 0 := by
    have htv : (1 / 2 : ℝ)
        * ∑ y, |coarsen (adaptivePartition g b) p y - g y| = 0 := h
    rcases mul_eq_zero.mp htv with h' | h'
    · norm_num at h'
    · exact h'
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun y _ => abs_nonneg _)).mp hsum
  have h01 : ∀ y, coarsen (adaptivePartition g b) p y = g y := by
    intro y
    have hy0 := hall y (Finset.mem_univ y)
    rw [abs_eq_zero, sub_eq_zero] at hy0
    exact hy0
  exact ⟨adaptivePartition g b, (funext h01).symm⟩

theorem mis_one {g p : Y → ℝ} (hp : IsProbVec p) (hg : IsProbVec g) :
    mis 1 g p = tvDist (fun _ => 1 / (Fintype.card Y : ℝ)) g := by
  classical
  have hidx : ∀ y, binIndex g 1 y = 0 := by
    intro y
    have h1 := (binIndex_spec hg le_rfl y).1
    exact Nat.lt_one_iff.mp h1
  have hpart : ∀ y, (adaptivePartition g 1).part y = Finset.univ := by
    intro y
    ext z
    simp only [Finset.mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      have h2 : (Setoid.ker (binIndex g 1)) y z := by
        change binIndex g 1 y = binIndex g 1 z
        rw [hidx y, hidx z]
      exact (Finpartition.mem_part_ofSetoid_iff_rel (a := y)
        (b := z)).mpr h2
  have hmain : coarsen (adaptivePartition g 1) p
      = fun _ => 1 / (Fintype.card Y : ℝ) := by
    funext y
    change (∑ z ∈ (adaptivePartition g 1).part y, p z)
        / ((adaptivePartition g 1).part y).card
        = 1 / (Fintype.card Y : ℝ)
    rw [hpart y, Finset.card_univ, hp.2]
  change tvDist (coarsen (adaptivePartition g 1) p) g = _
  rw [hmain]

/-- Lemma 2 for a finite mixture. Let `w` be a probability vector on a
finite type `ι`, each `p i` a probability vector on `Y`, `P` a partition of
`Y` (the same for every `i`), and `S ⊆ Y` nonempty. Writing
`q(A) = ∑ y ∈ A, q y` and `p_i^P` for the `P`-coarsening of `p i`,
`∑ i, w i * max (p_i(S) − p_i^P(S)) 0` is at most
`|Y \ S| * max_{y ∈ S} ∑ i, w i * p_i(y)`.
For `ν = ∑ i, w i δ_{p i}` this is the source's bound
`E_ν[(p(S) − p^Π(S))_+] ≤ |Y \ S| · max_{y ∈ S} E_ν[p(y)]`. -/
theorem expect_posPart_mass_sub_coarsen_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : IsProbVec w) (p : ι → Y → ℝ)
    (hp : ∀ i, IsProbVec (p i)) (P : Finpartition (Finset.univ : Finset Y))
    (S : Finset Y) (hS : S.Nonempty) :
    ∑ i, w i * max (∑ y ∈ S, p i y - ∑ y ∈ S, coarsen P (p i) y) 0
      ≤ (Finset.univ \ S).card *
        (S.image (fun y => ∑ i, w i * p i y)).max' (Finset.image_nonempty.mpr hS) := by
  have hM_nonneg : 0 ≤ (S.image (fun y => ∑ i, w i * p i y)).max'
      (Finset.image_nonempty.mpr hS) := by
    have hmem := Finset.max'_mem (S.image (fun y => ∑ i, w i * p i y))
      (Finset.image_nonempty.mpr hS)
    obtain ⟨y₀, -, hy₀'⟩ := Finset.mem_image.mp hmem
    have hy₀'' : (∑ i, w i * p i y₀)
        = (S.image (fun y => ∑ i, w i * p i y)).max'
          (Finset.image_nonempty.mpr hS) := hy₀'
    rw [← hy₀'']
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hw.1 i) ((hp i).1 y₀)
  have hM_ge : ∀ y ∈ S, (∑ i, w i * p i y)
      ≤ (S.image (fun y => ∑ i, w i * p i y)).max'
        (Finset.image_nonempty.mpr hS) := by
    intro y hy
    exact Finset.le_max' _ _
      (Finset.mem_image_of_mem (fun y => ∑ i, w i * p i y) hy)
  have hSun : S = P.parts.biUnion (fun t => t ∩ S) := by
    ext z
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · intro hz
      obtain ⟨t, ht, hzt⟩ := P.exists_mem (Finset.mem_univ z)
      exact ⟨t, ht, hzt, hz⟩
    · rintro ⟨t, ht, hzt, hz⟩
      exact hz
  have hdisjI : Set.PairwiseDisjoint (P.parts : Set (Finset Y))
      (fun t => t ∩ S) := by
    intro t ht u hu hne
    exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
      (P.disjoint ht hu hne)
  have hA : ∀ i, (∑ y ∈ S, p i y - ∑ y ∈ S, coarsen P (p i) y)
      = ∑ t ∈ P.parts, ((∑ y ∈ t ∩ S, p i y)
        - (∑ y ∈ t ∩ S, coarsen P (p i) y)) := by
    intro i
    conv_lhs => rw [hSun]
    rw [Finset.sum_biUnion hdisjI, Finset.sum_biUnion hdisjI,
      ← Finset.sum_sub_distrib]
  have hblk : ∀ i, ∀ t ∈ P.parts,
      max ((∑ y ∈ t ∩ S, p i y) - (∑ y ∈ t ∩ S, coarsen P (p i) y)) 0
        ≤ ((t \ S).card : ℝ) * (∑ y ∈ t ∩ S, p i y) / (t.card : ℝ) := by
    intro i t ht
    have hct : (0 : ℝ) < (t.card : ℝ) := by
      have hpos := Finset.card_pos.mpr (P.nonempty_of_mem_parts ht)
      exact Nat.cast_pos.mpr hpos
    have he0 : (0 : ℝ) ≤ ((t ∩ S).card : ℝ) := Nat.cast_nonneg _
    have hBp0 : (0 : ℝ) ≤ ∑ y ∈ t ∩ S, p i y := by
      apply Finset.sum_nonneg
      intro y _
      exact (hp i).1 y
    have hBq0 : (0 : ℝ) ≤ ∑ y ∈ t \ S, p i y := by
      apply Finset.sum_nonneg
      intro y _
      exact (hp i).1 y
    have hsplit : ∑ z ∈ t, p i z
        = (∑ z ∈ t ∩ S, p i z) + (∑ z ∈ t \ S, p i z) := by
      have h := Finset.sum_sdiff (s₁ := t ∩ S) (s₂ := t) (f := p i)
        (Finset.inter_subset_left)
      have heq : t \ (t ∩ S) = t \ S := by
        ext z
        simp only [Finset.mem_sdiff, Finset.mem_inter, not_and]
        tauto
      rw [heq, add_comm] at h
      exact h.symm
    have hBc : ∑ y ∈ t ∩ S, coarsen P (p i) y
        = ((t ∩ S).card : ℝ) * (((∑ z ∈ t ∩ S, p i z)
          + (∑ z ∈ t \ S, p i z)) / (t.card : ℝ)) := by
      have hterm : ∀ y ∈ t ∩ S,
          coarsen P (p i) y = (∑ z ∈ t, p i z) / (t.card : ℝ) := by
        intro y hy
        have hyt : y ∈ t := (Finset.mem_inter.mp hy).1
        have hpy : P.part y = t := P.part_eq_of_mem ht hyt
        change (∑ z ∈ P.part y, p i z) / (P.part y).card = _
        rw [hpy]
      have hsum : ∑ y ∈ t ∩ S, coarsen P (p i) y
          = ∑ _y ∈ t ∩ S, ((∑ z ∈ t, p i z) / (t.card : ℝ)) :=
        Finset.sum_congr rfl hterm
      rw [hsum, Finset.sum_const, nsmul_eq_mul, hsplit]
    have hcard : (t.card : ℝ)
        = ((t ∩ S).card : ℝ) + ((t \ S).card : ℝ) := by
      have h := Finset.card_sdiff_add_card_inter t S
      have hn : t.card = (t ∩ S).card + (t \ S).card := by omega
      exact_mod_cast hn
    have havg_ge : (∑ z ∈ t ∩ S, p i z) / (t.card : ℝ)
        ≤ ((∑ z ∈ t ∩ S, p i z) + (∑ z ∈ t \ S, p i z)) / (t.card : ℝ) := by
      have hdiff : ((∑ z ∈ t ∩ S, p i z) + (∑ z ∈ t \ S, p i z)) / (t.card : ℝ)
          - (∑ z ∈ t ∩ S, p i z) / (t.card : ℝ)
          = (∑ z ∈ t \ S, p i z) / (t.card : ℝ) := by
        rw [← sub_div]
        congr 1
        ring
      have hnn : (0 : ℝ) ≤ (∑ z ∈ t \ S, p i z) / (t.card : ℝ) :=
        div_nonneg hBq0 hct.le
      linarith [hdiff, hnn]
    have heq : (∑ y ∈ t ∩ S, p i y)
        - ((t ∩ S).card : ℝ) * ((∑ z ∈ t ∩ S, p i z) / (t.card : ℝ))
        = ((t \ S).card : ℝ) * (∑ y ∈ t ∩ S, p i y) / (t.card : ℝ) := by
      rw [eq_div_iff hct.ne', sub_mul, ← mul_div_assoc,
        div_mul_cancel₀ _ hct.ne', hcard]
      ring
    have hnn : (0 : ℝ)
        ≤ ((t \ S).card : ℝ) * (∑ y ∈ t ∩ S, p i y) / (t.card : ℝ) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) hBp0) hct.le
    have h2 : (∑ y ∈ t ∩ S, p i y)
        - ((t ∩ S).card : ℝ) * (((∑ z ∈ t ∩ S, p i z)
          + (∑ z ∈ t \ S, p i z)) / (t.card : ℝ))
        ≤ (∑ y ∈ t ∩ S, p i y)
          - ((t ∩ S).card : ℝ) * ((∑ z ∈ t ∩ S, p i z) / (t.card : ℝ)) := by
      have h1 : ((t ∩ S).card : ℝ) * ((∑ z ∈ t ∩ S, p i z) / (t.card : ℝ))
          ≤ ((t ∩ S).card : ℝ) * (((∑ z ∈ t ∩ S, p i z)
            + (∑ z ∈ t \ S, p i z)) / (t.card : ℝ)) :=
        mul_le_mul_of_nonneg_left havg_ge he0
      linarith [h1]
    rw [hBc]
    exact max_le_iff.mpr ⟨le_trans h2 (le_of_eq heq), hnn⟩
  have hper : ∀ i, w i * max (∑ y ∈ S, p i y - ∑ y ∈ S, coarsen P (p i) y) 0
      ≤ ∑ t ∈ P.parts, w i * ((((t \ S).card : ℝ)
        * (∑ y ∈ t ∩ S, p i y)) / (t.card : ℝ)) := by
    intro i
    have hmax : max (∑ y ∈ S, p i y - ∑ y ∈ S, coarsen P (p i) y) 0
        ≤ ∑ t ∈ P.parts, max ((∑ y ∈ t ∩ S, p i y)
          - (∑ y ∈ t ∩ S, coarsen P (p i) y)) 0 := by
      rw [hA i]
      apply max_le_iff.mpr
      constructor
      · apply Finset.sum_le_sum
        intro t _
        exact le_max_left _ _
      · apply Finset.sum_nonneg
        intro t _
        exact le_max_right _ _
    have hwi : 0 ≤ w i := hw.1 i
    calc w i * max (∑ y ∈ S, p i y - ∑ y ∈ S, coarsen P (p i) y) 0
        ≤ w i * (∑ t ∈ P.parts, max ((∑ y ∈ t ∩ S, p i y)
          - (∑ y ∈ t ∩ S, coarsen P (p i) y)) 0) :=
          mul_le_mul_of_nonneg_left hmax hwi
      _ = ∑ t ∈ P.parts, w i * max ((∑ y ∈ t ∩ S, p i y)
          - (∑ y ∈ t ∩ S, coarsen P (p i) y)) 0 :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ t ∈ P.parts, w i * ((((t \ S).card : ℝ)
          * (∑ y ∈ t ∩ S, p i y)) / (t.card : ℝ)) := by
          apply Finset.sum_le_sum
          intro t ht
          exact mul_le_mul_of_nonneg_left (hblk i t ht) hwi
  have hT : ∀ t ∈ P.parts,
      (∑ i, w i * ((((t \ S).card : ℝ) * (∑ y ∈ t ∩ S, p i y))
        / (t.card : ℝ)))
        ≤ ((t \ S).card : ℝ)
          * (S.image (fun y => ∑ i, w i * p i y)).max'
            (Finset.image_nonempty.mpr hS) := by
    intro t ht
    have hct : (0 : ℝ) < (t.card : ℝ) := by
      have hpos := Finset.card_pos.mpr (P.nonempty_of_mem_parts ht)
      exact Nat.cast_pos.mpr hpos
    have hTt_eq : (∑ i, w i * ((((t \ S).card : ℝ)
        * (∑ y ∈ t ∩ S, p i y)) / (t.card : ℝ)))
        = (((t \ S).card : ℝ) / (t.card : ℝ))
          * (∑ y ∈ t ∩ S, ∑ i, w i * p i y) := by
      have hterm : ∀ i ∈ Finset.univ, w i * ((((t \ S).card : ℝ)
          * (∑ y ∈ t ∩ S, p i y)) / (t.card : ℝ))
          = (((t \ S).card : ℝ) / (t.card : ℝ))
            * (w i * (∑ y ∈ t ∩ S, p i y)) := by
        intro i _
        ring
      have hmix_eq : (∑ i, w i * (∑ y ∈ t ∩ S, p i y))
          = ∑ y ∈ t ∩ S, ∑ i, w i * p i y := by
        have h1 : ∀ i ∈ Finset.univ, w i * (∑ y ∈ t ∩ S, p i y)
            = ∑ y ∈ t ∩ S, w i * p i y :=
          fun i _ => Finset.mul_sum _ _ _
        rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hmix_eq]
    have hsum_le : (∑ y ∈ t ∩ S, ∑ i, w i * p i y)
        ≤ ((t ∩ S).card : ℝ)
          * (S.image (fun y => ∑ i, w i * p i y)).max'
            (Finset.image_nonempty.mpr hS) := by
      have h1 : (∑ y ∈ t ∩ S, ∑ i, w i * p i y)
          ≤ ∑ _y ∈ t ∩ S, (S.image (fun y => ∑ i, w i * p i y)).max'
            (Finset.image_nonempty.mpr hS) := by
        apply Finset.sum_le_sum
        intro y hy
        exact hM_ge y (Finset.mem_inter.mp hy).2
      rw [Finset.sum_const, nsmul_eq_mul] at h1
      exact h1
    have het : ((t ∩ S).card : ℝ) ≤ (t.card : ℝ) := by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_left
    have hdiv1 : ((t ∩ S).card : ℝ) / (t.card : ℝ) ≤ 1 := by
      rw [div_le_one hct]
      exact het
    have hfrac : ((t \ S).card : ℝ) / (t.card : ℝ) * ((t ∩ S).card : ℝ)
        ≤ ((t \ S).card : ℝ) := by
      have h1 : ((t \ S).card : ℝ) * (((t ∩ S).card : ℝ) / (t.card : ℝ))
          ≤ ((t \ S).card : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hdiv1 (Nat.cast_nonneg _)
      rw [mul_one] at h1
      have heq : ((t \ S).card : ℝ) / (t.card : ℝ) * ((t ∩ S).card : ℝ)
          = ((t \ S).card : ℝ) * (((t ∩ S).card : ℝ) / (t.card : ℝ)) := by
        ring
      rw [heq]
      exact h1
    rw [hTt_eq]
    have hstep : (((t \ S).card : ℝ) / (t.card : ℝ))
        * (∑ y ∈ t ∩ S, ∑ i, w i * p i y)
        ≤ (((t \ S).card : ℝ) / (t.card : ℝ)) * (((t ∩ S).card : ℝ)
          * (S.image (fun y => ∑ i, w i * p i y)).max'
            (Finset.image_nonempty.mpr hS)) :=
      mul_le_mul_of_nonneg_left hsum_le
        (div_nonneg (Nat.cast_nonneg _) hct.le)
    have hfin : (((t \ S).card : ℝ) / (t.card : ℝ)) * (((t ∩ S).card : ℝ)
        * (S.image (fun y => ∑ i, w i * p i y)).max'
          (Finset.image_nonempty.mpr hS))
        ≤ ((t \ S).card : ℝ)
          * (S.image (fun y => ∑ i, w i * p i y)).max'
            (Finset.image_nonempty.mpr hS) := by
      have heq : (((t \ S).card : ℝ) / (t.card : ℝ)) * (((t ∩ S).card : ℝ)
          * (S.image (fun y => ∑ i, w i * p i y)).max'
            (Finset.image_nonempty.mpr hS))
          = ((((t \ S).card : ℝ) / (t.card : ℝ)) * ((t ∩ S).card : ℝ))
            * (S.image (fun y => ∑ i, w i * p i y)).max'
              (Finset.image_nonempty.mpr hS) := by
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hfrac hM_nonneg
    exact le_trans hstep hfin
  have hcardU : ∑ t ∈ P.parts, ((t \ S).card : ℝ)
      = ((Finset.univ \ S).card : ℝ) := by
    have hdecomp : Finset.univ \ S = P.parts.biUnion (fun t => t \ S) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_biUnion]
      constructor
      · intro hzS
        obtain ⟨t, ht, hzt⟩ := P.exists_mem (Finset.mem_univ z)
        exact ⟨t, ht, hzt, hzS⟩
      · rintro ⟨t, ht, hzt, hzS⟩
        exact hzS
    have hdisjD : Set.PairwiseDisjoint (P.parts : Set (Finset Y))
        (fun t => t \ S) := by
      intro t ht u hu hne
      exact Disjoint.mono Finset.sdiff_subset Finset.sdiff_subset
        (P.disjoint ht hu hne)
    conv_rhs => rw [hdecomp, Finset.card_eq_sum_ones,
      Finset.sum_biUnion hdisjD, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun t _ => by rw [Finset.card_eq_sum_ones])
  calc ∑ i, w i * max (∑ y ∈ S, p i y - ∑ y ∈ S, coarsen P (p i) y) 0
      ≤ ∑ i, ∑ t ∈ P.parts, w i * ((((t \ S).card : ℝ)
        * (∑ y ∈ t ∩ S, p i y)) / (t.card : ℝ)) :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = ∑ t ∈ P.parts, ∑ i, w i * ((((t \ S).card : ℝ)
        * (∑ y ∈ t ∩ S, p i y)) / (t.card : ℝ)) := by
        rw [Finset.sum_comm]
    _ ≤ ∑ t ∈ P.parts, ((t \ S).card : ℝ)
        * (S.image (fun y => ∑ i, w i * p i y)).max'
          (Finset.image_nonempty.mpr hS) :=
        Finset.sum_le_sum (fun t ht => hT t ht)
    _ = (Finset.univ \ S).card *
        (S.image (fun y => ∑ i, w i * p i y)).max'
          (Finset.image_nonempty.mpr hS) := by
        rw [← Finset.sum_mul, hcardU]

/-- Theorem 1 for a finite mixture. Let `w` be a probability vector on a
finite type `ι`, each `p i` and `g` probability vectors on `Y`, `P` a
partition of `Y`, `O ⊆ Y` with `U = Y \ O` nonempty, and `F i ⊆ Y` a fact
set for each component `i`. Writing `q(A) = ∑ y ∈ A, q y` and `p_i^P` for
the `P`-coarsening of `p i`,
`∑ i, w i * max (p_i(U) − ‖p_i^P − g‖_TV − g(Y \ F i)) 0` is at most
`max_{y ∈ U} ∑_{i : y ∈ F i} w i + |O| * max_{y ∈ U} ∑ i, w i * p_i(y)`.
For `ν = ∑ i, w i δ_{p i}` this is the source's bound
`E_{p∼ν}[(p(U) − ‖p^Π − g‖_TV − g(H))_+] ≤`
`max_{y ∈ U} Pr[y ∈ F] + |O| · max_{y ∈ U} E_ν[p(y)]` with `H = Y \ F`,
except that the fact set may differ between components and the source's
hypothesis `O ⊆ F` is not needed. -/
theorem expect_hallucination_gap_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : IsProbVec w) (p : ι → Y → ℝ)
    (hp : ∀ i, IsProbVec (p i))
    (O : Finset Y) (F : ι → Finset Y)
    (g : Y → ℝ) (hg : IsProbVec g) (P : Finpartition (Finset.univ : Finset Y))
    (hU : (Finset.univ \ O).Nonempty) :
    ∑ i, w i * max (∑ y ∈ Finset.univ \ O, p i y - tvDist (coarsen P (p i)) g
                      - ∑ y ∈ Finset.univ \ F i, g y) 0
      ≤ ((Finset.univ \ O).image
            (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)).max'
          (Finset.image_nonempty.mpr hU)
        + O.card * ((Finset.univ \ O).image (fun y => ∑ i, w i * p i y)).max'
          (Finset.image_nonempty.mpr hU) := by
  have hM1_nonneg : 0 ≤ ((Finset.univ \ O).image
      (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)).max'
      (Finset.image_nonempty.mpr hU) := by
    have hmem := Finset.max'_mem ((Finset.univ \ O).image
      (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i))
      (Finset.image_nonempty.mpr hU)
    obtain ⟨y₀, -, hy₀'⟩ := Finset.mem_image.mp hmem
    have hy₀'' : (∑ i ∈ Finset.univ.filter (fun i => y₀ ∈ F i), w i)
        = ((Finset.univ \ O).image
          (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)).max'
          (Finset.image_nonempty.mpr hU) := hy₀'
    rw [← hy₀'']
    apply Finset.sum_nonneg
    intro i _
    exact hw.1 i
  have hPr_le : ∀ y ∈ Finset.univ \ O,
      (∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)
        ≤ ((Finset.univ \ O).image
          (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)).max'
          (Finset.image_nonempty.mpr hU) := by
    intro y hy
    exact Finset.le_max' _ _
      (Finset.mem_image_of_mem
        (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i) hy)
  have hmass : ∀ i, ∑ y, coarsen P (p i) y = ∑ y, g y := by
    intro i
    rw [sum_coarsen, (hp i).2, hg.2]
  have hEq6 : ∀ i, (∑ y ∈ Finset.univ \ O, coarsen P (p i) y)
      - (∑ y ∈ Finset.univ \ O, g y)
      ≤ tvDist (coarsen P (p i)) g := by
    intro i
    exact sub_le_tvDist_of_sum_eq (hmass i) _
  have hsplitG : ∀ i, (∑ y ∈ Finset.univ \ O, g y)
      = (∑ y ∈ (Finset.univ \ O) ∩ F i, g y)
        + (∑ y ∈ (Finset.univ \ O) \ F i, g y) := by
    intro i
    have h := Finset.sum_sdiff (s₁ := (Finset.univ \ O) ∩ F i)
      (s₂ := Finset.univ \ O) (f := g) (Finset.inter_subset_left)
    have heq : (Finset.univ \ O) \ ((Finset.univ \ O) ∩ F i)
        = (Finset.univ \ O) \ F i := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_inter, not_and]
      tauto
    rw [heq, add_comm] at h
    exact h.symm
  have hsubG : ∀ i, (∑ y ∈ (Finset.univ \ O) \ F i, g y)
      ≤ ∑ y ∈ Finset.univ \ F i, g y := by
    intro i
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun y _ _ => hg.1 y)
    intro z hz
    rw [Finset.mem_sdiff] at hz ⊢
    exact ⟨Finset.mem_univ z, hz.2⟩
  have hGA : ∀ i, (∑ y ∈ Finset.univ \ O, p i y
      - tvDist (coarsen P (p i)) g - ∑ y ∈ Finset.univ \ F i, g y)
      ≤ ((∑ y ∈ Finset.univ \ O, p i y
        - ∑ y ∈ Finset.univ \ O, coarsen P (p i) y)
        + (∑ y ∈ (Finset.univ \ O) ∩ F i, g y)) := by
    intro i
    have h1 := hEq6 i
    have h2 := hsplitG i
    have h3 := hsubG i
    linarith [h1, h2, h3]
  have hmaxI : ∀ i, max (∑ y ∈ Finset.univ \ O, p i y
      - tvDist (coarsen P (p i)) g - ∑ y ∈ Finset.univ \ F i, g y) 0
      ≤ max ((∑ y ∈ Finset.univ \ O, p i y
        - ∑ y ∈ Finset.univ \ O, coarsen P (p i) y)) 0
        + (∑ y ∈ (Finset.univ \ O) ∩ F i, g y) := by
    intro i
    apply max_le_iff.mpr
    constructor
    · have hle : (∑ y ∈ Finset.univ \ O, p i y
          - ∑ y ∈ Finset.univ \ O, coarsen P (p i) y)
          ≤ max ((∑ y ∈ Finset.univ \ O, p i y
            - ∑ y ∈ Finset.univ \ O, coarsen P (p i) y)) 0 :=
          le_max_left _ _
      linarith [hGA i, hle]
    · have hB0 : (0 : ℝ) ≤ ∑ y ∈ (Finset.univ \ O) ∩ F i, g y := by
        apply Finset.sum_nonneg
        intro y _
        exact hg.1 y
      exact le_trans (le_max_right _ _) (le_add_of_nonneg_right hB0)
  have hcomb : ∀ i, w i * max (∑ y ∈ Finset.univ \ O, p i y
      - tvDist (coarsen P (p i)) g - ∑ y ∈ Finset.univ \ F i, g y) 0
      ≤ w i * max ((∑ y ∈ Finset.univ \ O, p i y
        - ∑ y ∈ Finset.univ \ O, coarsen P (p i) y)) 0
        + w i * (∑ y ∈ (Finset.univ \ O) ∩ F i, g y) := by
    intro i
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hmaxI i) (hw.1 i)
  have hUU : Finset.univ \ (Finset.univ \ O) = O := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
  have hL2 := expect_posPart_mass_sub_coarsen_le w hw p hp P
    (Finset.univ \ O) hU
  rw [hUU] at hL2
  have hE : (∑ i, w i * (∑ y ∈ (Finset.univ \ O) ∩ F i, g y))
      ≤ ((Finset.univ \ O).image
        (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)).max'
        (Finset.image_nonempty.mpr hU) := by
    have hinter : ∀ i, (Finset.univ \ O) ∩ F i
        = (Finset.univ \ O).filter (fun y => y ∈ F i) := by
      intro i
      ext z
      simp only [Finset.mem_inter, Finset.mem_filter]
    have hswap : (∑ i, w i * (∑ y ∈ (Finset.univ \ O) ∩ F i, g y))
        = ∑ y ∈ (Finset.univ \ O),
          g y * (∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i) := by
      have h1 : ∀ i ∈ Finset.univ, w i * (∑ y ∈ (Finset.univ \ O) ∩ F i, g y)
          = ∑ y ∈ (Finset.univ \ O),
            w i * (if y ∈ F i then g y else 0) := by
        intro i _
        rw [hinter i, Finset.sum_filter, Finset.mul_sum]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      have h2 : ∀ i ∈ Finset.univ, w i * (if y ∈ F i then g y else 0)
          = g y * (if y ∈ F i then w i else 0) := by
        intro i _
        by_cases hh : y ∈ F i <;> simp [hh, mul_comm]
      rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, Finset.sum_filter]
    rw [hswap]
    have hUg1 : (∑ y ∈ Finset.univ \ O, g y) ≤ 1 := by
      have hle := Finset.sum_le_sum_of_subset_of_nonneg (s := Finset.univ \ O)
        (t := Finset.univ) (f := g) Finset.sdiff_subset
        (fun y _ _ => hg.1 y)
      rw [hg.2] at hle
      exact hle
    calc ∑ y ∈ (Finset.univ \ O),
          g y * (∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)
        ≤ ∑ y ∈ (Finset.univ \ O), g y * (((Finset.univ \ O).image
          (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)).max'
          (Finset.image_nonempty.mpr hU)) := by
          apply Finset.sum_le_sum
          intro y hy
          exact mul_le_mul_of_nonneg_left (hPr_le y hy) (hg.1 y)
      _ = (∑ y ∈ Finset.univ \ O, g y) * (((Finset.univ \ O).image
          (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)).max'
          (Finset.image_nonempty.mpr hU)) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ 1 * (((Finset.univ \ O).image
          (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)).max'
          (Finset.image_nonempty.mpr hU)) :=
          mul_le_mul_of_nonneg_right hUg1 hM1_nonneg
      _ = ((Finset.univ \ O).image
          (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)).max'
          (Finset.image_nonempty.mpr hU) :=
          one_mul _
  calc ∑ i, w i * max (∑ y ∈ Finset.univ \ O, p i y
      - tvDist (coarsen P (p i)) g - ∑ y ∈ Finset.univ \ F i, g y) 0
      ≤ ∑ i, (w i * max ((∑ y ∈ Finset.univ \ O, p i y
        - ∑ y ∈ Finset.univ \ O, coarsen P (p i) y)) 0
        + w i * (∑ y ∈ (Finset.univ \ O) ∩ F i, g y)) :=
        Finset.sum_le_sum (fun i _ => hcomb i)
    _ = (∑ i, w i * max ((∑ y ∈ Finset.univ \ O, p i y
        - ∑ y ∈ Finset.univ \ O, coarsen P (p i) y)) 0)
        + (∑ i, w i * (∑ y ∈ (Finset.univ \ O) ∩ F i, g y)) :=
        Finset.sum_add_distrib
    _ ≤ ((O.card : ℝ) * ((Finset.univ \ O).image
        (fun y => ∑ i, w i * p i y)).max' (Finset.image_nonempty.mpr hU))
        + (((Finset.univ \ O).image
        (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)).max'
        (Finset.image_nonempty.mpr hU)) :=
        add_le_add hL2 hE
    _ = ((Finset.univ \ O).image
        (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)).max'
        (Finset.image_nonempty.mpr hU)
        + O.card * ((Finset.univ \ O).image
          (fun y => ∑ i, w i * p i y)).max'
          (Finset.image_nonempty.mpr hU) := by
        rw [add_comm]

/-- Theorem 1 with the two maxima replaced by bounds. Let `w` be a
probability vector on a finite type `ι`, each `p i` and `g` probability
vectors on `Y`, `P` a partition of `Y`, `O ⊆ Y` with `U = Y \ O` (possibly
empty), and `F i ⊆ Y` for each `i`. If `0 ≤ α`, `0 ≤ β`, and every `y ∈ U`
has `∑_{i : y ∈ F i} w i ≤ α` and `∑ i, w i * p_i(y) ≤ β`, then, writing
`q(A) = ∑ y ∈ A, q y` and `p_i^P` for the `P`-coarsening of `p i`,
`∑ i, w i * max (p_i(U) − ‖p_i^P − g‖_TV − g(Y \ F i)) 0 ≤ α + |O| * β`. -/
theorem expect_hallucination_gap_le_of_bounds {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : IsProbVec w) (p : ι → Y → ℝ)
    (hp : ∀ i, IsProbVec (p i))
    (O : Finset Y) (F : ι → Finset Y)
    (g : Y → ℝ) (hg : IsProbVec g) (P : Finpartition (Finset.univ : Finset Y))
    (α β : ℝ) (hα0 : 0 ≤ α) (hβ0 : 0 ≤ β)
    (hα : ∀ y ∈ Finset.univ \ O,
      ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i ≤ α)
    (hβ : ∀ y ∈ Finset.univ \ O, ∑ i, w i * p i y ≤ β) :
    ∑ i, w i * max (∑ y ∈ Finset.univ \ O, p i y - tvDist (coarsen P (p i)) g
                      - ∑ y ∈ Finset.univ \ F i, g y) 0
      ≤ α + O.card * β := by
  by_cases hU : (Finset.univ \ O).Nonempty
  · have hmain := expect_hallucination_gap_le w hw p hp O F g hg P hU
    have hM1 : ((Finset.univ \ O).image
        (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)).max'
        (Finset.image_nonempty.mpr hU) ≤ α := by
      rw [Finset.max'_le_iff]
      intro v hv
      obtain ⟨y, hyU, hyv⟩ := Finset.mem_image.mp hv
      rw [← hyv]
      exact hα y hyU
    have hM2 : ((Finset.univ \ O).image
        (fun y => ∑ i, w i * p i y)).max'
        (Finset.image_nonempty.mpr hU) ≤ β := by
      rw [Finset.max'_le_iff]
      intro v hv
      obtain ⟨y, hyU, hyv⟩ := Finset.mem_image.mp hv
      rw [← hyv]
      exact hβ y hyU
    have hle : ((Finset.univ \ O).image
        (fun y => ∑ i ∈ Finset.univ.filter (fun i => y ∈ F i), w i)).max'
        (Finset.image_nonempty.mpr hU)
        + O.card * ((Finset.univ \ O).image
          (fun y => ∑ i, w i * p i y)).max'
          (Finset.image_nonempty.mpr hU)
        ≤ α + O.card * β :=
      add_le_add hM1 (mul_le_mul_of_nonneg_left hM2 (Nat.cast_nonneg _))
    exact le_trans hmain hle
  · have hUe : Finset.univ \ O = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hU
    have htv0 : ∀ i, (0 : ℝ) ≤ tvDist (coarsen P (p i)) g := by
      intro i
      change (0 : ℝ) ≤ (1 / 2 : ℝ) * ∑ y, |coarsen P (p i) y - g y|
      apply mul_nonneg
      · norm_num
      · apply Finset.sum_nonneg
        intro y _
        exact abs_nonneg _
    have hper : ∀ i, w i * max (∑ y ∈ Finset.univ \ O, p i y
        - tvDist (coarsen P (p i)) g - ∑ y ∈ Finset.univ \ F i, g y) 0
        = 0 := by
      intro i
      have hgsum0 : (0 : ℝ) ≤ ∑ y ∈ Finset.univ \ F i, g y := by
        apply Finset.sum_nonneg
        intro y _
        exact hg.1 y
      rw [hUe, Finset.sum_empty]
      have hle : (0 : ℝ) - tvDist (coarsen P (p i)) g
          - ∑ y ∈ Finset.univ \ F i, g y ≤ 0 := by
        linarith [htv0 i, hgsum0]
      rw [max_eq_right hle, mul_zero]
    have hLHS : (∑ i, w i * max (∑ y ∈ Finset.univ \ O, p i y
        - tvDist (coarsen P (p i)) g - ∑ y ∈ Finset.univ \ F i, g y) 0)
        = 0 := by
      rw [Finset.sum_congr rfl (fun i _ => hper i)]
      exact Finset.sum_const_zero
    rw [hLHS]
    exact add_nonneg hα0 (mul_nonneg (Nat.cast_nonneg _) hβ0)

/-- Boundary case of Theorem 1 with everything observed, `O = Y`, so that
`U = ∅` and `p_i(U) = 0`. For any weights `w`, any functions `p i`, any fact
sets `F i`, any partition `P` of `Y` and any probability vector `g`,
`∑ i, w i * max (p_i(U) − ‖p_i^P − g‖_TV − g(Y \ F i)) 0 = 0`, writing
`q(A) = ∑ y ∈ A, q y`, `‖q − g‖_TV = (1/2) ∑ y, |q y − g y|` and `p_i^P` for
the `P`-coarsening of `p i`. -/
theorem expect_hallucination_gap_eq_zero_of_eq_univ {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (p : ι → Y → ℝ) (F : ι → Finset Y)
    (g : Y → ℝ) (hg : IsProbVec g) (P : Finpartition (Finset.univ : Finset Y)) :
    ∑ i, w i * max (∑ y ∈ Finset.univ \ Finset.univ, p i y
                      - tvDist (coarsen P (p i)) g
                      - ∑ y ∈ Finset.univ \ F i, g y) 0 = 0 := by
  have htv0 : ∀ i, (0 : ℝ) ≤ tvDist (coarsen P (p i)) g := by
    intro i
    change (0 : ℝ) ≤ (1 / 2 : ℝ) * ∑ y, |coarsen P (p i) y - g y|
    apply mul_nonneg
    · norm_num
    · apply Finset.sum_nonneg
      intro y _
      exact abs_nonneg _
  have hU : (Finset.univ \ Finset.univ : Finset Y) = ∅ := by simp
  have hper : ∀ i, w i * max (∑ y ∈ Finset.univ \ Finset.univ, p i y
      - tvDist (coarsen P (p i)) g - ∑ y ∈ Finset.univ \ F i, g y) 0
      = 0 := by
    intro i
    have hgsum0 : (0 : ℝ) ≤ ∑ y ∈ Finset.univ \ F i, g y := by
      apply Finset.sum_nonneg
      intro y _
      exact hg.1 y
    rw [hU, Finset.sum_empty]
    have hle : (0 : ℝ) - tvDist (coarsen P (p i)) g
        - ∑ y ∈ Finset.univ \ F i, g y ≤ 0 := by
      linarith [htv0 i, hgsum0]
    rw [max_eq_right hle, mul_zero]
  calc (∑ i, w i * max (∑ y ∈ Finset.univ \ Finset.univ, p i y
      - tvDist (coarsen P (p i)) g - ∑ y ∈ Finset.univ \ F i, g y) 0)
      = ∑ i ∈ Finset.univ, (0 : ℝ) :=
        Finset.sum_congr rfl (fun i _ => hper i)
    _ = 0 := Finset.sum_const_zero

end MainTheorem

section WorldModel

variable {Y : Type*} [Fintype Y] [DecidableEq Y] {X : Type*} [Fintype X]

/-- Pushforward of `D : X → ℝ` along `f : X → Y`: `y ↦ ∑_{x : f x = y} D x`,
defined for every `D`. When `D` is a probability vector on `X` (a document
distribution), this is the source's induced factoid distribution `p = f ∘ D_L`. -/
noncomputable def pushforward (f : X → Y) (D : X → ℝ) : Y → ℝ :=
  fun y => ∑ x ∈ Finset.univ.filter (fun x => f x = y), D x

/-- `∏ k, D (x k)`: when `D` is a probability vector on `X`, the probability
of drawing the sample `x = (x 1, …, x n)` independently from `D`. -/
noncomputable def trainProb {n : ℕ} (D : X → ℝ) (x : Fin n → X) : ℝ :=
  ∏ k, D (x k)

/-- The facts `F = {y | 0 < p y} ∪ {⊥}` for `p = pushforward f D`, defined for
every `D : X → ℝ`. When `D` is a probability vector (a document distribution),
`{y | 0 < p y}` is the support of `p`, the image under `f` of the support of
`D`, and `F` is the source's set of facts `f(supp(D)) ∪ {⊥}` of the world `D`. -/
noncomputable def facts (f : X → Y) (bot : Y) (D : X → ℝ) : Finset Y :=
  Finset.univ.filter (fun y => 0 < pushforward f D y) ∪ {bot}

/-- The hallucinations `H = Y \ F` for `F = facts f bot D`, defined for every
`D : X → ℝ`; when `D` is a probability vector, these are the source's
hallucinations of the world `D`. -/
noncomputable def hallucinations (f : X → Y) (bot : Y) (D : X → ℝ) : Finset Y :=
  Finset.univ \ facts f bot D

/-- The observed factoids of a sample `x : Fin n → X` (Eq. (4)):
`O = {f (x k) | k} ∪ {⊥}`. -/
def observed (f : X → Y) (bot : Y) {n : ℕ} (x : Fin n → X) : Finset Y :=
  Finset.univ.image (f ∘ x) ∪ {bot}

/-- The monofact rate of Eq. (5): the number of factoids `y ≠ ⊥` that occur
exactly once among `f (x 1), …, f (x n)`, divided by `n` (so `0` when
`n = 0`). -/
noncomputable def monofactRate (f : X → Y) (bot : Y) {n : ℕ} (x : Fin n → X) : ℝ :=
  ((Finset.univ.filter
    (fun y => y ≠ bot ∧ (Finset.univ.filter (fun k => f (x k) = y)).card = 1)).card : ℝ) / n

/-- `s`-sparse facts for weights `w i` on worlds `D i`, defined for any `w` and
`D`: every world with `0 < w i` has `|F| ≤ e^{-s} |H|`, for
`F = facts f bot (D i)` and `H = hallucinations f bot (D i)`. When `w` and every
`D i` are probability vectors, this is Assumption 1 for the prior that draws the
world `D i` with probability `w i`: with probability one, `|F| ≤ e^{-s} |H|`. -/
def IsSparse (f : X → Y) (bot : Y) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (D : ι → X → ℝ) (s : ℝ) : Prop :=
  ∀ i, 0 < w i → ((facts f bot (D i)).card : ℝ)
    ≤ Real.exp (-s) * (hallucinations f bot (D i)).card

/-- Regular facts, cross-multiplied, defined for any weights `w` and functions
`D i`: for every sample `x : Fin n → X` with `0 < ∑ i, w i * P_i(x)`, where
`P_i(x) = trainProb (D i) x`, and all `y, y'` outside `observed f bot x`,
`∑_{i : y ∈ F_i} w i * P_i(x) = ∑_{i : y' ∈ F_i} w i * P_i(x)` for
`F_i = facts f bot (D i)`. When `w` and every `D i` are probability vectors,
this is Definition 3 (see `hasRegularFacts_iff`). -/
def HasRegularFacts (f : X → Y) (bot : Y) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (D : ι → X → ℝ) (n : ℕ) : Prop :=
  ∀ x : Fin n → X, 0 < ∑ i, w i * trainProb (D i) x →
    ∀ y ∉ observed f bot x, ∀ y' ∉ observed f bot x,
      ∑ i ∈ Finset.univ.filter (fun i => y ∈ facts f bot (D i)),
          w i * trainProb (D i) x
        = ∑ i ∈ Finset.univ.filter (fun i => y' ∈ facts f bot (D i)),
          w i * trainProb (D i) x

/-- Regular probabilities, cross-multiplied, defined for any weights `w` and
functions `D i`: for every sample `x : Fin n → X` with `0 < ∑ i, w i * P_i(x)`,
where `P_i(x) = trainProb (D i) x`, and all `y, y'` outside `observed f bot x`,
`∑ i, w i * P_i(x) * p_i(y) = ∑ i, w i * P_i(x) * p_i(y')` for
`p_i = pushforward f (D i)`. When `w` and every `D i` are probability vectors,
this is Definition 4 (see `hasRegularProbabilities_iff`). -/
def HasRegularProbabilities (f : X → Y) (bot : Y) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (D : ι → X → ℝ) (n : ℕ) : Prop :=
  ∀ x : Fin n → X, 0 < ∑ i, w i * trainProb (D i) x →
    ∀ y ∉ observed f bot x, ∀ y' ∉ observed f bot x,
      ∑ i, w i * trainProb (D i) x * pushforward f (D i) y
        = ∑ i, w i * trainProb (D i) x * pushforward f (D i) y'

/-- Regularity: both `HasRegularFacts` and `HasRegularProbabilities` hold. When
`w` and every `D i` are probability vectors, these are Definitions 3 and 4, and
this is the source's regularity. -/
def IsRegular (f : X → Y) (bot : Y) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (D : ι → X → ℝ) (n : ℕ) : Prop :=
  HasRegularFacts f bot w D n ∧ HasRegularProbabilities f bot w D n

/-- `HasRegularFacts` is equivalent to its divided form, for any weights `w` and
functions `D i`: for every sample `x` with `Z = ∑ i, w i * P_i(x) > 0`, where
`P_i(x) = trainProb (D i) x`, and all `y, y'` outside `observed f bot x`,
`(∑_{i : y ∈ F_i} w i * P_i(x)) / Z = (∑_{i : y' ∈ F_i} w i * P_i(x)) / Z`, for
`F_i = facts f bot (D i)`. When `w` and every `D i` are probability vectors,
`Z` is the probability of drawing the sample `x` and each quotient is a
conditional probability, so this is the conditional form of Definition 3,
`Pr[y ∈ F | x] = Pr[y' ∈ F | x]`. -/
theorem hasRegularFacts_iff (f : X → Y) (bot : Y) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (D : ι → X → ℝ) (n : ℕ) :
    HasRegularFacts f bot w D n ↔
      ∀ x : Fin n → X, 0 < ∑ i, w i * trainProb (D i) x →
        ∀ y ∉ observed f bot x, ∀ y' ∉ observed f bot x,
          (∑ i ∈ Finset.univ.filter (fun i => y ∈ facts f bot (D i)),
              w i * trainProb (D i) x) / (∑ i, w i * trainProb (D i) x)
            = (∑ i ∈ Finset.univ.filter (fun i => y' ∈ facts f bot (D i)),
              w i * trainProb (D i) x) / (∑ i, w i * trainProb (D i) x) := by
  constructor
  · intro h x hx y hy y' hy'
    have h1 : (∑ i ∈ Finset.univ.filter (fun i => y ∈ facts f bot (D i)),
          w i * trainProb (D i) x)
        = (∑ i ∈ Finset.univ.filter (fun i => y' ∈ facts f bot (D i)),
          w i * trainProb (D i) x) :=
      h x hx y hy y' hy'
    rw [h1]
  · intro h x hx y hy y' hy'
    have hden : (∑ i, w i * trainProb (D i) x) ≠ 0 := ne_of_gt hx
    have h1 := h x hx y hy y' hy'
    have h2 : ((∑ i ∈ Finset.univ.filter (fun i => y ∈ facts f bot (D i)),
          w i * trainProb (D i) x) / (∑ i, w i * trainProb (D i) x))
        * (∑ i, w i * trainProb (D i) x)
        = ((∑ i ∈ Finset.univ.filter (fun i => y' ∈ facts f bot (D i)),
          w i * trainProb (D i) x) / (∑ i, w i * trainProb (D i) x))
        * (∑ i, w i * trainProb (D i) x) := by
      rw [h1]
    rw [div_mul_cancel₀ _ hden, div_mul_cancel₀ _ hden] at h2
    exact h2

end WorldModel

section RegularProbabilitiesBridge

variable {Y : Type*} [DecidableEq Y] {X : Type*} [Fintype X]

/-- `HasRegularProbabilities` is equivalent to its divided form, for any weights
`w` and functions `D i`: for every sample `x` with `Z = ∑ i, w i * P_i(x) > 0`,
where `P_i(x) = trainProb (D i) x`, and all `y, y'` outside `observed f bot x`,
`(∑ i, w i * P_i(x) * p_i(y)) / Z = (∑ i, w i * P_i(x) * p_i(y')) / Z`, for
`p_i = pushforward f (D i)`. When `w` and every `D i` are probability vectors,
`Z` is the probability of drawing the sample `x` and each quotient is a
conditional expectation, so this is the conditional form of Definition 4,
`E[p(y) | x] = E[p(y') | x]`. -/
theorem hasRegularProbabilities_iff (f : X → Y) (bot : Y) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (D : ι → X → ℝ) (n : ℕ) :
    HasRegularProbabilities f bot w D n ↔
      ∀ x : Fin n → X, 0 < ∑ i, w i * trainProb (D i) x →
        ∀ y ∉ observed f bot x, ∀ y' ∉ observed f bot x,
          (∑ i, w i * trainProb (D i) x * pushforward f (D i) y)
              / (∑ i, w i * trainProb (D i) x)
            = (∑ i, w i * trainProb (D i) x * pushforward f (D i) y')
              / (∑ i, w i * trainProb (D i) x) := by
  constructor
  · intro h x hx y hy y' hy'
    have h1 : (∑ i, w i * trainProb (D i) x * pushforward f (D i) y)
        = (∑ i, w i * trainProb (D i) x * pushforward f (D i) y') :=
      h x hx y hy y' hy'
    rw [h1]
  · intro h x hx y hy y' hy'
    have hden : (∑ i, w i * trainProb (D i) x) ≠ 0 := ne_of_gt hx
    have h1 := h x hx y hy y' hy'
    have h2 : ((∑ i, w i * trainProb (D i) x * pushforward f (D i) y)
          / (∑ i, w i * trainProb (D i) x))
        * (∑ i, w i * trainProb (D i) x)
        = ((∑ i, w i * trainProb (D i) x * pushforward f (D i) y')
          / (∑ i, w i * trainProb (D i) x))
        * (∑ i, w i * trainProb (D i) x) := by
      rw [h1]
    rw [div_mul_cancel₀ _ hden, div_mul_cancel₀ _ hden] at h2
    exact h2

end RegularProbabilitiesBridge

end CalibratedHallucination
end MachineLearning
end Cslib
