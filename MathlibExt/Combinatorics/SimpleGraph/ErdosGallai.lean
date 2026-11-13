/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Int.Star
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

@[expose] public section

section
namespace MathlibExt.Combinatorics.SimpleGraph.ErdosGallaiWanted

/-!
# Erdős–Gallai theorem

Graphical degree-sequence characterization via subset inequalities.
-/

set_option maxHeartbeats 1000000 in
-- Large maximal-subrealization proof needs more heartbeats than default.
-- The many explicit graph-move constructions exceed 200000 heartbeats.
/--
**Erdős–Gallai theorem.** Let $V$ be a finite set and $d \colon V \to \mathbb{N}$. There is a
simple graph on $V$ in which every vertex $v$ has degree $d(v)$ if and only if the sum
$\sum_{v \in V} d(v)$ is even and, for every subset $S \subseteq V$,
$$\sum_{v \in S} d(v) \le |S|(|S| - 1) + \sum_{v \in V \setminus S} \min(d(v), |S|).$$

Source: P. Erdős and T. Gallai, Graphs with prescribed degrees of vertices,
Matematikai Lapok 11 (1960), 264-274.

Proves `Wanted` entry `erdos_gallai`.
-/
theorem erdos_gallai {V : Type*} [Fintype V] [DecidableEq V]
    (d : V → ℕ) :
    (∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj, ∀ v, G.degree v = d v) ↔
      Even (∑ v : V, d v) ∧
        ∀ S : Finset V,
          ∑ v ∈ S, d v ≤ S.card * (S.card - 1) +
            ∑ v ∈ Finset.univ \ S, min (d v) S.card := by
  classical
  constructor
  · -- Necessity: a realizing graph implies evenness and the subset inequalities.
    rintro ⟨G, hdec, hG⟩
    have hsum : ∑ v : V, d v = 2 * G.edgeFinset.card := by
      have hA : ∑ v : V, d v = ∑ v : V, G.degree v :=
        Finset.sum_congr rfl (fun v _ => (hG v).symm)
      have hB : ∑ v : V, G.degree v = 2 * G.edgeFinset.card :=
        @SimpleGraph.sum_degrees_eq_twice_card_edges V G _ hdec
      exact hA.trans hB
    refine ⟨⟨G.edgeFinset.card, by omega⟩, ?_⟩
    intro S
    have hdeg : ∀ v : V, (G.neighborFinset v).card = d v := by
      intro v
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hG v
    have hsplit : ∀ v ∈ S, (G.neighborFinset v).card
        = ((G.neighborFinset v).filter (· ∈ S)).card
          + ((G.neighborFinset v).filter (· ∉ S)).card := by
      intro v _
      have hunion : (G.neighborFinset v).filter (· ∈ S)
            ∪ (G.neighborFinset v).filter (· ∉ S) = G.neighborFinset v := by
        ext w
        simp only [Finset.mem_union, Finset.mem_filter]
        tauto
      have hdisj : Disjoint ((G.neighborFinset v).filter (· ∈ S))
          ((G.neighborFinset v).filter (· ∉ S)) := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        rw [Finset.mem_filter] at hw1 hw2
        exact hw2.2 hw1.2
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hinside : ∀ v ∈ S, ((G.neighborFinset v).filter (· ∈ S)).card
        ≤ S.card - 1 := by
      intro v hv
      have hsub : (G.neighborFinset v).filter (· ∈ S) ⊆ S.erase v := by
        intro w hw
        rw [Finset.mem_filter] at hw
        rw [Finset.mem_erase]
        constructor
        · intro hcontr
          subst hcontr
          rw [SimpleGraph.mem_neighborFinset] at hw
          exact absurd rfl (G.ne_of_adj hw.1)
        · exact hw.2
      calc ((G.neighborFinset v).filter (· ∈ S)).card
          ≤ (S.erase v).card := Finset.card_le_card hsub
        _ = S.card - 1 := Finset.card_erase_of_mem hv
    have hcross : ∑ v ∈ S, ((G.neighborFinset v).filter (· ∉ S)).card
        = ∑ w ∈ Finset.univ \ S, ((G.neighborFinset w).filter (· ∈ S)).card := by
      have key : ∀ v ∈ S, ((G.neighborFinset v).filter (· ∉ S)).card
          = ∑ w ∈ Finset.univ \ S, (if G.Adj v w then 1 else 0) := by
        intro v _
        have e1 : (G.neighborFinset v).filter (· ∉ S)
            = (Finset.univ \ S).filter (fun w => G.Adj v w) := by
          ext w
          simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
            Finset.mem_sdiff, Finset.mem_univ]
          tauto
        rw [e1, Finset.card_eq_sum_ones, Finset.sum_filter]
      have key2 : ∀ w ∈ Finset.univ \ S,
          (∑ v ∈ S, (if G.Adj v w then 1 else 0))
            = ((G.neighborFinset w).filter (· ∈ S)).card := by
        intro w _
        have e2 : (G.neighborFinset w).filter (· ∈ S)
            = S.filter (fun v => G.Adj v w) := by
          ext v
          simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
          tauto
        rw [e2, Finset.card_eq_sum_ones, Finset.sum_filter]
      calc ∑ v ∈ S, ((G.neighborFinset v).filter (· ∉ S)).card
          = ∑ v ∈ S, ∑ w ∈ Finset.univ \ S, (if G.Adj v w then 1 else 0) :=
            Finset.sum_congr rfl (fun v hv => key v hv)
        _ = ∑ w ∈ Finset.univ \ S, ∑ v ∈ S, (if G.Adj v w then 1 else 0) :=
            Finset.sum_comm
        _ = ∑ w ∈ Finset.univ \ S, ((G.neighborFinset w).filter (· ∈ S)).card :=
            Finset.sum_congr rfl (fun w hw => key2 w hw)
    have hmin : ∀ w ∈ Finset.univ \ S, ((G.neighborFinset w).filter (· ∈ S)).card
        ≤ min (d w) S.card := by
      intro w _
      refine le_min ?_ ?_
      · calc ((G.neighborFinset w).filter (· ∈ S)).card
            ≤ (G.neighborFinset w).card := Finset.card_filter_le _ _
        _ = d w := hdeg w
      · apply Finset.card_le_card
        intro x hx
        rw [Finset.mem_filter] at hx
        exact hx.2
    calc ∑ v ∈ S, d v
        = ∑ v ∈ S, (((G.neighborFinset v).filter (· ∈ S)).card
            + ((G.neighborFinset v).filter (· ∉ S)).card) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [← hsplit v hv, hdeg v]
      _ = (∑ v ∈ S, ((G.neighborFinset v).filter (· ∈ S)).card)
          + (∑ v ∈ S, ((G.neighborFinset v).filter (· ∉ S)).card) :=
          Finset.sum_add_distrib
      _ ≤ S.card * (S.card - 1)
          + ∑ w ∈ Finset.univ \ S, min (d w) S.card := by
          apply Nat.add_le_add
          · calc ∑ v ∈ S, ((G.neighborFinset v).filter (· ∈ S)).card
                ≤ ∑ v ∈ S, (S.card - 1) :=
                  Finset.sum_le_sum (fun v hv => hinside v hv)
              _ = S.card * (S.card - 1) := by
                  rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
          · rw [hcross]
            exact Finset.sum_le_sum (fun w hw => hmin w hw)
  · -- Sufficiency: evenness plus the subset inequalities imply realizability.
    rintro ⟨heven, hineq⟩
    by_cases hempty : IsEmpty V
    · refine ⟨⊥, Classical.decRel _, ?_⟩
      intro v
      exact (hempty.false v).elim
    · rw [not_isEmpty_iff] at hempty
      -- Tie-breaking key (hint (a)).
      set key : V → ℕ := fun v => d v * Fintype.card V + (Fintype.equivFin V v).val
        with hkey
      have hk : ∀ v : V, key v
          = d v * Fintype.card V + (Fintype.equivFin V v).val := fun v => rfl
      have e_inj : Function.Injective (Fintype.equivFin V) :=
        (Fintype.equivFin V).injective
      have e_lt : ∀ v : V, (Fintype.equivFin V v).val < Fintype.card V :=
        fun v => Fin.is_lt _
      have key_lt_of_d_lt : ∀ {v w : V}, d v < d w → key v < key w := by
        intro v w h
        have e1 : (Fintype.equivFin V v).val < Fintype.card V := e_lt v
        have h1 : d v * Fintype.card V + (Fintype.equivFin V v).val
            < d v * Fintype.card V + Fintype.card V := by
          omega
        have h2 : d v * Fintype.card V + Fintype.card V
            ≤ d w * Fintype.card V := by
          have hle : d v + 1 ≤ d w := h
          calc d v * Fintype.card V + Fintype.card V
              = (d v + 1) * Fintype.card V := by ring
            _ ≤ d w * Fintype.card V := Nat.mul_le_mul hle (le_refl _)
        have h3 : d w * Fintype.card V
            ≤ d w * Fintype.card V + (Fintype.equivFin V w).val :=
          Nat.le_add_right _ _
        have hv : key v
            = d v * Fintype.card V + (Fintype.equivFin V v).val := hk v
        have hw : key w
            = d w * Fintype.card V + (Fintype.equivFin V w).val := hk w
        omega
      have key_ge_of_lt : ∀ {v w : V}, key v < key w → d v ≤ d w := by
        intro v w hlt
        by_contra hle
        have hle' : d w < d v := lt_of_not_ge hle
        exact absurd (key_lt_of_d_lt hle') (not_lt_of_gt hlt)
      have key_inj : Function.Injective key := by
        intro v w h
        by_contra hne
        rcases lt_trichotomy (d v) (d w) with hlt | heq | hgt
        · have hlt' := key_lt_of_d_lt hlt
          omega
        · have hv : key v
              = d v * Fintype.card V + (Fintype.equivFin V v).val := hk v
          have hw : key w
              = d w * Fintype.card V + (Fintype.equivFin V w).val := hk w
          rw [← heq] at hw
          have hev : (Fintype.equivFin V v).val
              = (Fintype.equivFin V w).val := by omega
          exact hne (e_inj (Fin.val_injective hev))
        · have hgt' := key_lt_of_d_lt hgt
          omega
      -- Subrealizations and the maximal one (hint (b)).
      -- Degrees are tracked via `Set.ncard` of neighbor sets, which needs no
      -- `DecidableRel` instance (this avoids an instance mismatch between the
      -- classical `H.degree` used for a variable graph and the computable
      -- `Bot.adjDecidable`-based `degree` of `⊥`).
      set Smax : Finset (SimpleGraph V) :=
        Finset.univ.filter (fun H => ∀ v, (H.neighborSet v).ncard ≤ d v) with hSmax
      have hbot_mem : (⊥ : SimpleGraph V) ∈ Smax := by
        rw [hSmax, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro v
        have h1 : (⊥ : SimpleGraph V).neighborSet v = ∅ :=
          SimpleGraph.neighborSet_bot
        rw [h1]
        simp
      obtain ⟨H, hHmem, hHmax⟩ := Finset.exists_max_image Smax
        (fun H => ∑ v, 2 ^ key v * (H.neighborSet v).ncard) ⟨⊥, hbot_mem⟩
      have hHle : ∀ v, (H.neighborSet v).ncard ≤ d v :=
        (Finset.mem_filter.mp hHmem).2
      -- Comparison principle with a dropping vertex (hint (c)).
      have cmp : ∀ (H' : SimpleGraph V),
          (∀ v, (H'.neighborSet v).ncard ≤ d v) →
          ∀ (x z : V), key z < key x →
          (H.neighborSet x).ncard + 1 ≤ (H'.neighborSet x).ncard →
          (H.neighborSet z).ncard ≤ (H'.neighborSet z).ncard + 1 →
          (∀ v, v ≠ x → v ≠ z → (H.neighborSet v).ncard ≤ (H'.neighborSet v).ncard) →
          (∑ v, 2 ^ key v * (H.neighborSet v).ncard)
            < (∑ v, 2 ^ key v * (H'.neighborSet v).ncard) := by
        intro H' hH' x z hzx hx hz hrest
        have hxz : x ≠ z := fun h => (ne_of_gt hzx) (congrArg key h)
        have h2lt : (2 : ℤ) ^ key z < (2 : ℤ) ^ key x := by
          have h := Nat.pow_lt_pow_right (show (1 : ℕ) < 2 by norm_num) hzx
          exact_mod_cast h
        have hFx : (2 : ℤ) ^ key x
            ≤ (2 : ℤ) ^ key x * (((H'.neighborSet x).ncard : ℤ)
              - ((H.neighborSet x).ncard : ℤ)) := by
          have h1 : (1 : ℤ) ≤ ((H'.neighborSet x).ncard : ℤ)
              - ((H.neighborSet x).ncard : ℤ) := by
            have hx' : ((H.neighborSet x).ncard : ℤ) + 1
                ≤ ((H'.neighborSet x).ncard : ℤ) := by
              exact_mod_cast hx
            linarith
          calc (2 : ℤ) ^ key x = (2 : ℤ) ^ key x * 1 := by ring
            _ ≤ _ := by gcongr
        have hFz : -((2 : ℤ) ^ key z)
            ≤ (2 : ℤ) ^ key z * (((H'.neighborSet z).ncard : ℤ)
              - ((H.neighborSet z).ncard : ℤ)) := by
          have h1 : (-1 : ℤ) ≤ ((H'.neighborSet z).ncard : ℤ)
              - ((H.neighborSet z).ncard : ℤ) := by
            have hz' : ((H.neighborSet z).ncard : ℤ)
                ≤ ((H'.neighborSet z).ncard : ℤ) + 1 := by
              exact_mod_cast hz
            linarith
          calc -((2 : ℤ) ^ key z) = (2 : ℤ) ^ key z * (-1) := by ring
            _ ≤ _ := by gcongr
        have hF : ∀ v : V, v ≠ x → v ≠ z →
            (0 : ℤ) ≤ (2 : ℤ) ^ key v * (((H'.neighborSet v).ncard : ℤ)
              - ((H.neighborSet v).ncard : ℤ)) := by
          intro v h1 h2
          apply mul_nonneg (pow_nonneg (by norm_num) _)
          have hle : ((H.neighborSet v).ncard : ℤ)
              ≤ ((H'.neighborSet v).ncard : ℤ) := by
            exact_mod_cast hrest v h1 h2
          linarith
        have hdiff : (∑ v, (2 : ℤ) ^ key v * ((H'.neighborSet v).ncard : ℤ))
              - (∑ v, (2 : ℤ) ^ key v * ((H.neighborSet v).ncard : ℤ))
            = ∑ v, (2 : ℤ) ^ key v * (((H'.neighborSet v).ncard : ℤ)
              - ((H.neighborSet v).ncard : ℤ)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro v _
          ring
        have hpair : (2 : ℤ) ^ key x * (((H'.neighborSet x).ncard : ℤ)
                - ((H.neighborSet x).ncard : ℤ))
              + (2 : ℤ) ^ key z * (((H'.neighborSet z).ncard : ℤ)
                - ((H.neighborSet z).ncard : ℤ))
            = ∑ v ∈ ({x, z} : Finset V),
                (2 : ℤ) ^ key v * (((H'.neighborSet v).ncard : ℤ)
                  - ((H.neighborSet v).ncard : ℤ)) :=
          by rw [Finset.sum_pair hxz]
        have hlb : (2 : ℤ) ^ key x - (2 : ℤ) ^ key z
            ≤ ∑ v, (2 : ℤ) ^ key v * (((H'.neighborSet v).ncard : ℤ)
              - ((H.neighborSet v).ncard : ℤ)) := by
          have hsub := Finset.sum_le_sum_of_subset_of_nonneg
            (s := ({x, z} : Finset V)) (t := Finset.univ) (Finset.subset_univ _)
            (fun v _ hvs => by
              simp only [Finset.mem_insert, Finset.mem_singleton] at hvs
              have hx1 : v ≠ x := fun h => hvs (Or.inl h)
              have hz1 : v ≠ z := fun h => hvs (Or.inr h)
              exact hF v hx1 hz1)
          linarith [hsub, hpair, hFx, hFz]
        have hc1 : ((∑ v, 2 ^ key v * (H.neighborSet v).ncard : ℕ) : ℤ)
            = ∑ v, (2 : ℤ) ^ key v * ((H.neighborSet v).ncard : ℤ) := by
          push_cast
          ring
        have hc2 : ((∑ v, 2 ^ key v * (H'.neighborSet v).ncard : ℕ) : ℤ)
            = ∑ v, (2 : ℤ) ^ key v * ((H'.neighborSet v).ncard : ℤ) := by
          push_cast
          ring
        omega
      -- Comparison principle with no dropping vertex (hint (c)).
      have cmp0 : ∀ (H' : SimpleGraph V),
          (∀ v, (H'.neighborSet v).ncard ≤ d v) →
          ∀ (x : V), (H.neighborSet x).ncard + 1 ≤ (H'.neighborSet x).ncard →
          (∀ v, v ≠ x → (H.neighborSet v).ncard ≤ (H'.neighborSet v).ncard) →
          (∑ v, 2 ^ key v * (H.neighborSet v).ncard)
            < (∑ v, 2 ^ key v * (H'.neighborSet v).ncard) := by
        intro H' hH' x hx hrest
        have hFx : (2 : ℤ) ^ key x
            ≤ (2 : ℤ) ^ key x * (((H'.neighborSet x).ncard : ℤ)
              - ((H.neighborSet x).ncard : ℤ)) := by
          have h1 : (1 : ℤ) ≤ ((H'.neighborSet x).ncard : ℤ)
              - ((H.neighborSet x).ncard : ℤ) := by
            have hx' : ((H.neighborSet x).ncard : ℤ) + 1
                ≤ ((H'.neighborSet x).ncard : ℤ) := by
              exact_mod_cast hx
            linarith
          calc (2 : ℤ) ^ key x = (2 : ℤ) ^ key x * 1 := by ring
            _ ≤ _ := by gcongr
        have hF : ∀ v : V, v ≠ x →
            (0 : ℤ) ≤ (2 : ℤ) ^ key v * (((H'.neighborSet v).ncard : ℤ)
              - ((H.neighborSet v).ncard : ℤ)) := by
          intro v h1
          apply mul_nonneg (pow_nonneg (by norm_num) _)
          have hle : ((H.neighborSet v).ncard : ℤ)
              ≤ ((H'.neighborSet v).ncard : ℤ) := by
            exact_mod_cast hrest v h1
          linarith
        have hdiff : (∑ v, (2 : ℤ) ^ key v * ((H'.neighborSet v).ncard : ℤ))
              - (∑ v, (2 : ℤ) ^ key v * ((H.neighborSet v).ncard : ℤ))
            = ∑ v, (2 : ℤ) ^ key v * (((H'.neighborSet v).ncard : ℤ)
              - ((H.neighborSet v).ncard : ℤ)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro v _
          ring
        have hsingle : (2 : ℤ) ^ key x * (((H'.neighborSet x).ncard : ℤ)
                - ((H.neighborSet x).ncard : ℤ))
            = ∑ v ∈ ({x} : Finset V),
                (2 : ℤ) ^ key v * (((H'.neighborSet v).ncard : ℤ)
                  - ((H.neighborSet v).ncard : ℤ)) :=
          by rw [Finset.sum_singleton]
        have hlb : (0 : ℤ)
            < ∑ v, (2 : ℤ) ^ key v * (((H'.neighborSet v).ncard : ℤ)
              - ((H.neighborSet v).ncard : ℤ)) := by
          have hsub := Finset.sum_le_sum_of_subset_of_nonneg
            (s := ({x} : Finset V)) (t := Finset.univ) (Finset.subset_univ _)
            (fun v _ hvs => by
              simp only [Finset.mem_singleton] at hvs
              exact hF v hvs)
          have hpos : (0 : ℤ) < (2 : ℤ) ^ key x := by positivity
          linarith [hsub, hsingle, hFx, hpos]
        have hc1 : ((∑ v, 2 ^ key v * (H.neighborSet v).ncard : ℕ) : ℤ)
            = ∑ v, (2 : ℤ) ^ key v * ((H.neighborSet v).ncard : ℤ) := by
          push_cast
          ring
        have hc2 : ((∑ v, 2 ^ key v * (H'.neighborSet v).ncard : ℕ) : ℤ)
            = ∑ v, (2 : ℤ) ^ key v * ((H'.neighborSet v).ncard : ℤ) := by
          push_cast
          ring
        omega
      -- It remains to show H saturates every vertex (hints (L), (P), C0-C3).
      have hsat_nc : ∀ v, (H.neighborSet v).ncard = d v := by
        by_contra hcon
        rw [not_forall] at hcon
        obtain ⟨v0, hv0⟩ := hcon
        -- D is the set of deficient vertices; it is nonempty.
        set D : Finset V := Finset.univ.filter
          (fun v => (H.neighborSet v).ncard < d v) with hD
        have hDmem : v0 ∈ D := by
          rw [hD, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hle : (H.neighborSet v0).ncard ≤ d v0 := hHle v0
          omega
        -- x is the element of D with the largest key.
        obtain ⟨x, hxD, hxmax⟩ := Finset.exists_max_image D key ⟨v0, hDmem⟩
        have hxmem : x ∈ Finset.univ.filter
            (fun u => (H.neighborSet u).ncard < d u) := by
          rw [← hD]
          exact hxD
        have hxlt : (H.neighborSet x).ncard < d x :=
          (Finset.mem_filter.mp hxmem).2
        -- (L) Neighbor lemma: a saturated vertex v ≠ x with d x ≤ d v
        -- has a neighbor u with u ≠ x and ¬ Adj x u.
        have hL : ∀ v : V, v ≠ x → (H.neighborSet v).ncard = d v →
            d x ≤ d v → ∃ u, H.Adj v u ∧ u ≠ x ∧ ¬ H.Adj x u := by
          intro v hne hsatv hdx
          by_contra hcon
          have hcon2 : ∀ w, H.Adj v w → w ≠ x → H.Adj x w := by
            intro w hw hne2
            by_contra hadj
            exact hcon ⟨w, hw, hne2, hadj⟩
          have hxnot : x ∉ H.neighborSet x :=
            fun h => (H.ne_of_adj h) rfl
          have hne_v : v ∉ H.neighborSet v :=
            fun h => (H.ne_of_adj h) rfl
          by_cases hadj : H.Adj v x
          · have hsub : H.neighborSet v
                ⊆ insert x (H.neighborSet x \ {v}) := by
              intro w hw
              simp only [Set.mem_insert_iff, Set.mem_sdiff,
                Set.mem_singleton_iff]
              by_cases heq : w = x
              · exact Or.inl heq
              · refine Or.inr ⟨hcon2 w hw heq, ?_⟩
                intro hvv
                rw [hvv] at hw
                exact hne_v hw
            have hle1 : (H.neighborSet v).ncard
                ≤ (insert x (H.neighborSet x \ {v})).ncard :=
              Set.ncard_le_ncard hsub (Set.toFinite _)
            have hnotmem : x ∉ H.neighborSet x \ {v} := by
              simp only [Set.mem_sdiff, Set.mem_singleton_iff]
              exact fun h => hxnot h.1
            have hcard : (insert x (H.neighborSet x \ {v})).ncard
                = (H.neighborSet x \ {v}).ncard + 1 :=
              Set.ncard_insert_of_notMem hnotmem
            have hmem_v : v ∈ H.neighborSet x := H.adj_symm hadj
            have hcard2 : (H.neighborSet x \ {v}).ncard + 1
                = (H.neighborSet x).ncard := by
              have hfinx : (H.neighborSet x).Finite := Set.toFinite _
              have h := Set.ncard_sdiff_singleton_add_one hmem_v hfinx
              omega
            have hle : (H.neighborSet v).ncard
                ≤ (H.neighborSet x).ncard := by omega
            omega
          · have hsub : H.neighborSet v ⊆ H.neighborSet x := by
              intro w hw
              by_cases heq : w = x
              · subst heq
                exact absurd hw hadj
              · exact hcon2 w hw heq
            have hle : (H.neighborSet v).ncard
                ≤ (H.neighborSet x).ncard :=
              Set.ncard_le_ncard hsub (Set.toFinite _)
            omega
        -- eps is the deficit at x.
        have heps_pos : 1 ≤ d x - (H.neighborSet x).ncard := by omega
        -- (P) Parity lemma: if eps = 1, another deficient vertex lies below x.
        have hP : d x - (H.neighborSet x).ncard = 1 →
            ∃ y, y ≠ x ∧ (H.neighborSet y).ncard < d y ∧ key y < key x := by
          intro heps1
          by_contra hcon
          have hsat_rest : ∀ y, y ≠ x → (H.neighborSet y).ncard = d y := by
            intro y hne
            by_contra hne_eq
            have hlt : (H.neighborSet y).ncard < d y :=
              lt_of_le_of_ne (hHle y) hne_eq
            have hyD : y ∈ D := by
              rw [hD, Finset.mem_filter]
              exact ⟨Finset.mem_univ _, hlt⟩
            have hle : key y ≤ key x := hxmax y hyD
            have hne_key : key y ≠ key x := fun h => hne (key_inj h)
            have hlt_key : key y < key x := lt_of_le_of_ne hle hne_key
            exact hcon ⟨y, hne, hlt, hlt_key⟩
          have hgap : ∀ y, y ≠ x → d y - (H.neighborSet y).ncard = 0 := by
            intro y hne
            have h := hsat_rest y hne
            omega
          have hsum_gap : ∑ v, (d v - (H.neighborSet v).ncard) = 1 := by
            have h1 : ∑ v ∈ (Finset.univ : Finset V),
                (d v - (H.neighborSet v).ncard)
                = d x - (H.neighborSet x).ncard := by
              apply Finset.sum_eq_single_of_mem x (Finset.mem_univ x)
              intro b _ hb
              exact hgap b hb
            rw [h1]
            exact heps1
          have hdeg_sum :=
            @SimpleGraph.sum_degrees_eq_twice_card_edges V H _ inferInstance
          have hsum_nc : ∑ v, (H.neighborSet v).ncard
              = 2 * H.edgeFinset.card := by
            rw [← hdeg_sum]
            apply Finset.sum_congr rfl
            intro v _
            exact SimpleGraph.ncard_neighborSet H v
          have hsplit : ∀ v : V, d v
              = (H.neighborSet v).ncard + (d v - (H.neighborSet v).ncard) := by
            intro v
            have h := hHle v
            omega
          have htotal : ∑ v : V, d v = 2 * H.edgeFinset.card + 1 := by
            have e1 : ∑ v : V, d v
                = ∑ v : V, ((H.neighborSet v).ncard
                  + (d v - (H.neighborSet v).ncard)) :=
              Finset.sum_congr rfl (fun v _ => hsplit v)
            rw [e1, Finset.sum_add_distrib, hsum_nc, hsum_gap]
          obtain ⟨k, hk⟩ := heven
          omega
        -- T is the set of vertices with key >= key x; r = |T|.
        set T : Finset V := Finset.univ.filter
          (fun v => key x ≤ key v) with hT
        set r : ℕ := T.card with hr
        have hxT : x ∈ T := by
          rw [hT, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, le_refl _⟩
        have hTmem : ∀ v : V, v ∈ T ↔ key x ≤ key v := by
          intro v
          constructor
          · intro hv
            rw [hT, Finset.mem_filter] at hv
            exact hv.2
          · intro hle
            rw [hT, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hle⟩
        have hTout : ∀ w : V, w ∉ T → key w < key x := by
          intro w hw
          have h : ¬ key x ≤ key w :=
            fun hle => hw ((hTmem w).mpr hle)
          exact not_le.mp h
        have hTdx : ∀ v : V, v ∈ T → d x ≤ d v := by
          intro v hv
          have hle : key x ≤ key v := (hTmem v).mp hv
          by_contra hcon
          have hlt : d v < d x := not_le.mp hcon
          have hkey : key v < key x := key_lt_of_d_lt hlt
          omega
        have hTsat : ∀ v : V, v ∈ T → v ≠ x →
            (H.neighborSet v).ncard = d v := by
          intro v hv hne
          have hle := hHle v
          by_contra hne_eq
          have hlt : (H.neighborSet v).ncard < d v :=
            lt_of_le_of_ne hle hne_eq
          have hvD : v ∈ D := by
            rw [hD, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hlt⟩
          have hle_key : key v ≤ key x := hxmax v hvD
          have hge_key : key x ≤ key v := (hTmem v).mp hv
          have heq : key v = key x :=
            le_antisymm hle_key hge_key
          exact hne (key_inj heq)
        have hr_pos : 1 ≤ r := by
          have hne : T.Nonempty := ⟨x, hxT⟩
          have hpos : 0 < T.card := Finset.card_pos.mpr hne
          omega
        -- C0: x is adjacent to every other deficient vertex.
        have hC0 : ∀ y : V, y ≠ x →
            (H.neighborSet y).ncard < d y → H.Adj x y := by
          intro y hyne hylt
          by_contra hnad
          have hxy_ne : x ≠ y := fun h => hyne h.symm
          let H' : SimpleGraph V :=
            { Adj := fun a b =>
                H.Adj a b ∨ ((a = x ∧ b = y) ∨ (a = y ∧ b = x))
              symm := ⟨by
                intro a b h
                rcases h with h1 | h1
                · exact Or.inl (H.adj_symm h1)
                · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
                  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
              loopless := ⟨by
                intro a h
                rcases h with h1 | h1
                · exact H.ne_of_adj h1 rfl
                · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · exact hxy_ne rfl
                  · exact hxy_ne rfl.symm⟩ }
          have heq_x : H'.neighborSet x =
              insert y (H.neighborSet x) := by
            ext w
            simp only [SimpleGraph.neighborSet, Set.mem_insert_iff]
            constructor
            · rintro (h1 | ⟨_, rfl⟩ | ⟨hcontra, _⟩)
              · exact Or.inr h1
              · exact Or.inl rfl
              · exact absurd hcontra hxy_ne
            · rintro (rfl | h1)
              · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
              · exact Or.inl h1
          have heq_y : H'.neighborSet y =
              insert x (H.neighborSet y) := by
            ext w
            simp only [SimpleGraph.neighborSet, Set.mem_insert_iff]
            constructor
            · rintro (h1 | ⟨hcontra, _⟩ | ⟨_, rfl⟩)
              · exact Or.inr h1
              · exact absurd hcontra hyne
              · exact Or.inl rfl
            · rintro (rfl | h1)
              · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
              · exact Or.inl h1
          have heq_o : ∀ v : V, v ≠ x → v ≠ y →
              H'.neighborSet v = H.neighborSet v := by
            intro v hvx hvy
            ext w
            simp only [SimpleGraph.neighborSet]
            constructor
            · rintro (h1 | ⟨h1a, _⟩ | ⟨h1a, _⟩)
              · exact h1
              · exact absurd h1a hvx
              · exact absurd h1a hvy
            · intro h1
              exact Or.inl h1
          have hmem_xy : y ∉ H.neighborSet x := hnad
          have hmem_yx : x ∉ H.neighborSet y :=
            fun h => hnad (H.adj_symm h)
          have hcard_x : (H'.neighborSet x).ncard =
              (H.neighborSet x).ncard + 1 := by
            rw [heq_x, Set.ncard_insert_of_notMem hmem_xy]
          have hcard_y : (H'.neighborSet y).ncard =
              (H.neighborSet y).ncard + 1 := by
            rw [heq_y, Set.ncard_insert_of_notMem hmem_yx]
          have hcard_o : ∀ v : V, v ≠ x → v ≠ y →
              (H'.neighborSet v).ncard =
              (H.neighborSet v).ncard := by
            intro v hvx hvy
            rw [heq_o v hvx hvy]
          have hH'le : ∀ v, (H'.neighborSet v).ncard ≤ d v := by
            intro v
            by_cases hvx : v = x
            · subst hvx
              omega
            · by_cases hvy : v = y
              · subst hvy
                omega
              · have h := hcard_o v hvx hvy
                have hle := hHle v
                omega
          have hH'mem : H' ∈ Smax := by
            rw [hSmax, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, hH'le⟩
          have hx_inc : (H.neighborSet x).ncard + 1 ≤
              (H'.neighborSet x).ncard := by
            omega
          have hrest : ∀ v : V, v ≠ x →
              (H.neighborSet v).ncard ≤
              (H'.neighborSet v).ncard := by
            intro v hvx
            by_cases hvy : v = y
            · subst hvy
              omega
            · have h := hcard_o v hvx hvy
              omega
          have hlt := cmp0 H' hH'le x hx_inc hrest
          have hle := hHmax H' hH'mem
          omega
        -- C1: x is adjacent to every v in T other than x.
        have hC1 : ∀ v : V, v ∈ T → v ≠ x → H.Adj x v := by
          intro v hvT hvx
          by_contra hnad
          have hsatv : (H.neighborSet v).ncard = d v :=
            hTsat v hvT hvx
          have hdxv : d x ≤ d v := hTdx v hvT
          obtain ⟨u, huv, hux_ne, hnux⟩ := hL v hvx hsatv hdxv
          have hvu_ne : v ≠ u := H.ne_of_adj huv
          have huv_ne : u ≠ v := fun h => hvu_ne h.symm
          have hxu_ne : x ≠ u := fun h => hux_ne h.symm
          have hxv_ne : x ≠ v := fun h => hvx h.symm
          have hnvu : ¬ H.Adj v x :=
            fun h => hnad (H.adj_symm h)
          have hnux' : ¬ H.Adj u x :=
            fun h => hnux (H.adj_symm h)
          have heps : d x - (H.neighborSet x).ncard = 1 ∨
              2 ≤ d x - (H.neighborSet x).ncard := by
            omega
          rcases heps with heps1 | heps2
          · -- eps = 1: remove uv and xy, add ux and vx.
            obtain ⟨y, hyne, hylt, hkey_y⟩ := hP heps1
            have hadj_xy : H.Adj x y := hC0 y hyne hylt
            have hyu_ne : y ≠ u := by
              intro hcon
              rw [hcon] at hadj_xy
              exact hnux hadj_xy
            have hkey_v : key x ≤ key v := (hTmem v).mp hvT
            have hyv_ne : y ≠ v := by
              intro hcon
              have heq : key y = key v := congrArg key hcon
              omega
            have hxy_ne : x ≠ y := fun h => hyne h.symm
            have huy_ne : u ≠ y := fun h => hyu_ne h.symm
            have hvy_ne : v ≠ y := fun h => hyv_ne h.symm
            have hmem_yx0 : y ∈ H.neighborSet x := hadj_xy
            have hmem_xy0 : x ∈ H.neighborSet y :=
              H.adj_symm hadj_xy
            let H' : SimpleGraph V :=
              { Adj := fun a b =>
                  (H.Adj a b ∧
                    ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u) ∨
                      (a = x ∧ b = y) ∨ (a = y ∧ b = x))) ∨
                  ((a = u ∧ b = x) ∨ (a = x ∧ b = u) ∨
                    (a = v ∧ b = x) ∨ (a = x ∧ b = v))
                symm := ⟨by
                  intro a b h
                  rcases h with ⟨h1, h2⟩ | h1
                  · refine Or.inl ⟨H.adj_symm h1, ?_⟩
                    intro hcon
                    apply h2
                    rcases hcon with
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                    · exact Or.inl ⟨rfl, rfl⟩
                    · exact Or.inr
                        (Or.inr (Or.inr ⟨rfl, rfl⟩))
                    · exact Or.inr
                        (Or.inr (Or.inl ⟨rfl, rfl⟩))
                  · rcases h1 with
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                    · exact Or.inr
                        (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
                    · exact Or.inr
                        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
                loopless := ⟨by
                  intro a h
                  rcases h with ⟨h1, _⟩ | h1
                  · exact H.ne_of_adj h1 rfl
                  · rcases h1 with
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact hux_ne rfl
                    · exact hux_ne rfl.symm
                    · exact hvx rfl
                    · exact hvx rfl.symm⟩ }
            have heq_x : H'.neighborSet x =
                insert v
                  (insert u ((H.neighborSet x) \ {y})) := by
              ext w
              simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                Set.mem_sdiff, Set.mem_singleton_iff]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨_, rfl⟩ |
                  ⟨hcontra2, _⟩ | ⟨_, rfl⟩)
                · by_cases heq : w = y
                  · subst heq
                    exact absurd
                      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) h2
                  · exact Or.inr (Or.inr ⟨h1, heq⟩)
                · exact absurd hcontra hxu_ne
                · exact Or.inr (Or.inl rfl)
                · exact absurd hcontra2 hxv_ne
                · exact Or.inl rfl
              · rintro (rfl | rfl | ⟨h1, hne⟩)
                · exact Or.inr
                    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
                · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                · refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨_, heq⟩ | ⟨hcontra3, _⟩)
                  · exact hxu_ne hcontra
                  · exact hxv_ne hcontra2
                  · exact hne heq
                  · exact hxy_ne hcontra3
            have heq_y : H'.neighborSet y =
                (H.neighborSet y) \ {x} := by
              ext w
              simp only [SimpleGraph.neighborSet,
                Set.mem_sdiff, Set.mem_singleton_iff]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                  ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                · by_cases heq : w = x
                  · subst heq
                    exact absurd
                      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) h2
                  · exact ⟨h1, heq⟩
                · exact absurd hcontra hyu_ne
                · exact absurd hcontra2 hyne
                · exact absurd hcontra3 hyv_ne
                · exact absurd hcontra4 hyne
              · rintro ⟨h1, hne⟩
                refine Or.inl ⟨h1, ?_⟩
                rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                  ⟨hcontra3, _⟩ | ⟨_, heq⟩)
                · exact hyu_ne hcontra
                · exact hyv_ne hcontra2
                · exact hyne hcontra3
                · exact hne heq
            have heq_u : H'.neighborSet u =
                insert x ((H.neighborSet u) \ {v}) := by
              ext w
              simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                Set.mem_sdiff, Set.mem_singleton_iff]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨_, rfl⟩ | ⟨hcontra, _⟩ |
                  ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                · by_cases heq : w = v
                  · subst heq
                    exact absurd (Or.inl ⟨rfl, rfl⟩) h2
                  · exact Or.inr ⟨h1, heq⟩
                · exact Or.inl rfl
                · exact absurd hcontra hux_ne
                · exact absurd hcontra2 huv_ne
                · exact absurd hcontra3 hux_ne
              · rintro (rfl | ⟨h1, hne⟩)
                · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                · refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨_, heq⟩ | ⟨hcontra, _⟩ |
                    ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                  · exact hne heq
                  · exact huv_ne hcontra
                  · exact hux_ne hcontra2
                  · exact huy_ne hcontra3
            have heq_v : H'.neighborSet v =
                insert x ((H.neighborSet v) \ {u}) := by
              ext w
              simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                Set.mem_sdiff, Set.mem_singleton_iff]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                  ⟨_, rfl⟩ | ⟨hcontra3, _⟩)
                · by_cases heq : w = u
                  · subst heq
                    exact absurd
                      (Or.inr (Or.inl ⟨rfl, rfl⟩)) h2
                  · exact Or.inr ⟨h1, heq⟩
                · exact absurd hcontra hvu_ne
                · exact absurd hcontra2 hvx
                · exact Or.inl rfl
                · exact absurd hcontra3 hvx
              · rintro (rfl | ⟨h1, hne⟩)
                · exact Or.inr
                    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
                · refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨_, heq⟩ |
                    ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                  · exact hvu_ne hcontra
                  · exact hne heq
                  · exact hvx hcontra2
                  · exact hvy_ne hcontra3
            have heq_o : ∀ p : V, p ≠ x → p ≠ u → p ≠ v →
                p ≠ y → H'.neighborSet p = H.neighborSet p := by
              intro p hpx hpu hpv hpy
              ext w
              simp only [SimpleGraph.neighborSet]
              constructor
              · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                  ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                · exact h1
                · exact absurd hcontra hpu
                · exact absurd hcontra2 hpx
                · exact absurd hcontra3 hpv
                · exact absurd hcontra4 hpx
              · intro h1
                refine Or.inl ⟨h1, ?_⟩
                rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                  ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                · exact hpu hcontra
                · exact hpv hcontra2
                · exact hpx hcontra3
                · exact hpy hcontra4
            have hmem_ux : u ∉ H.neighborSet x := hnux
            have hmem_vx : v ∉ H.neighborSet x := hnad
            have hmem_xu : x ∉ H.neighborSet u := hnux'
            have hmem_vu : v ∈ H.neighborSet u := H.adj_symm huv
            have hmem_xv : x ∉ H.neighborSet v := hnvu
            have hmem_uv : u ∈ H.neighborSet v := huv
            have hmem_u2 : u ∉ (H.neighborSet x) \ {y} :=
              fun h => hmem_ux h.1
            have hmem_v3 :
                v ∉ insert u ((H.neighborSet x) \ {y}) := by
              simp only [Set.mem_insert_iff, not_or]
              constructor
              · exact hvu_ne
              · exact fun h => hmem_vx h.1
            have hcard_x : (H'.neighborSet x).ncard =
                (H.neighborSet x).ncard + 1 := by
              rw [heq_x]
              have h1 := Set.ncard_insert_of_notMem hmem_v3
              have h2 := Set.ncard_insert_of_notMem hmem_u2
              have h3 := Set.ncard_sdiff_singleton_add_one hmem_yx0
                (Set.toFinite _)
              omega
            have hcard_y : (H'.neighborSet y).ncard + 1 =
                (H.neighborSet y).ncard := by
              rw [heq_y]
              exact Set.ncard_sdiff_singleton_add_one hmem_xy0
                (Set.toFinite _)
            have hcard_u : (H'.neighborSet u).ncard =
                (H.neighborSet u).ncard := by
              rw [heq_u]
              exact Set.ncard_exchange hmem_xu hmem_vu
            have hcard_v : (H'.neighborSet v).ncard =
                (H.neighborSet v).ncard := by
              rw [heq_v]
              exact Set.ncard_exchange hmem_xv hmem_uv
            have hcard_o : ∀ p : V, p ≠ x → p ≠ u → p ≠ v →
                p ≠ y → (H'.neighborSet p).ncard =
                (H.neighborSet p).ncard := by
              intro p hpx hpu hpv hpy
              rw [heq_o p hpx hpu hpv hpy]
            have hH'le : ∀ w, (H'.neighborSet w).ncard ≤ d w := by
              intro w
              by_cases hwx : w = x
              · rw [hwx]
                have hle_x := hHle x
                omega
              · by_cases hwy : w = y
                · rw [hwy]
                  have hle_y := hHle y
                  omega
                · by_cases hwu : w = u
                  · rw [hwu]
                    have hle_u := hHle u
                    omega
                  · by_cases hwv : w = v
                    · rw [hwv]
                      have hle_v := hHle v
                      omega
                    · have h := hcard_o w hwx hwu hwv hwy
                      have hle := hHle w
                      omega
            have hH'mem : H' ∈ Smax := by
              rw [hSmax, Finset.mem_filter]
              exact ⟨Finset.mem_univ _, hH'le⟩
            have hx_inc : (H.neighborSet x).ncard + 1 ≤
                (H'.neighborSet x).ncard := by
              omega
            have hy_le : (H.neighborSet y).ncard ≤
                (H'.neighborSet y).ncard + 1 := by
              omega
            have hrest : ∀ w : V, w ≠ x → w ≠ y →
                (H.neighborSet w).ncard ≤
                (H'.neighborSet w).ncard := by
              intro w hwx hwy
              by_cases hwu : w = u
              · rw [hwu]
                omega
              · by_cases hwv : w = v
                · rw [hwv]
                  omega
                · have h := hcard_o w hwx hwu hwv hwy
                  omega
            have hlt := cmp H' hH'le x y hkey_y hx_inc hy_le hrest
            have hle := hHmax H' hH'mem
            omega
          · -- eps >= 2: remove uv, add ux and vx.
            let H' : SimpleGraph V :=
              { Adj := fun a b =>
                  (H.Adj a b ∧
                    ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∨
                  ((a = u ∧ b = x) ∨ (a = x ∧ b = u) ∨
                    (a = v ∧ b = x) ∨ (a = x ∧ b = v))
                symm := ⟨by
                  intro a b h
                  rcases h with ⟨h1, h2⟩ | h1
                  · refine Or.inl ⟨H.adj_symm h1, ?_⟩
                    intro hcon
                    apply h2
                    rcases hcon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact Or.inr ⟨rfl, rfl⟩
                    · exact Or.inl ⟨rfl, rfl⟩
                  · rcases h1 with
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                    · exact Or.inr
                        (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
                    · exact Or.inr
                        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
                loopless := ⟨by
                  intro a h
                  rcases h with ⟨h1, _⟩ | h1
                  · exact H.ne_of_adj h1 rfl
                  · rcases h1 with
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact hux_ne rfl
                    · exact hux_ne rfl.symm
                    · exact hvx rfl
                    · exact hvx rfl.symm⟩ }
            have heq_x : H'.neighborSet x =
                insert v (insert u (H.neighborSet x)) := by
              ext w
              simp only [SimpleGraph.neighborSet, Set.mem_insert_iff]
              constructor
              · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨_, rfl⟩ |
                  ⟨hcontra2, _⟩ | ⟨_, rfl⟩)
                · exact Or.inr (Or.inr h1)
                · exact absurd hcontra hxu_ne
                · exact Or.inr (Or.inl rfl)
                · exact absurd hcontra2 hxv_ne
                · exact Or.inl rfl
              · rintro (rfl | rfl | h1)
                · exact Or.inr
                    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
                · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                · refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩)
                  · exact hxu_ne hcontra
                  · exact hxv_ne hcontra2
            have heq_u : H'.neighborSet u =
                insert x ((H.neighborSet u) \ {v}) := by
              ext w
              simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                Set.mem_sdiff, Set.mem_singleton_iff]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨_, rfl⟩ | ⟨hcontra, _⟩ |
                  ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                · by_cases heq : w = v
                  · subst heq
                    exact absurd (Or.inl ⟨rfl, rfl⟩) h2
                  · exact Or.inr ⟨h1, heq⟩
                · exact Or.inl rfl
                · exact absurd hcontra hux_ne
                · exact absurd hcontra2 huv_ne
                · exact absurd hcontra3 hux_ne
              · rintro (rfl | ⟨h1, hne⟩)
                · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                · refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨_, heq⟩ | ⟨hcontra, _⟩)
                  · exact hne heq
                  · exact huv_ne hcontra
            have heq_v : H'.neighborSet v =
                insert x ((H.neighborSet v) \ {u}) := by
              ext w
              simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                Set.mem_sdiff, Set.mem_singleton_iff]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                  ⟨_, rfl⟩ | ⟨hcontra3, _⟩)
                · by_cases heq : w = u
                  · subst heq
                    exact absurd (Or.inr ⟨rfl, rfl⟩) h2
                  · exact Or.inr ⟨h1, heq⟩
                · exact absurd hcontra hvu_ne
                · exact absurd hcontra2 hvx
                · exact Or.inl rfl
                · exact absurd hcontra3 hvx
              · rintro (rfl | ⟨h1, hne⟩)
                · exact Or.inr
                    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
                · refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨_, heq⟩)
                  · exact hvu_ne hcontra
                  · exact hne heq
            have heq_o : ∀ p : V, p ≠ x → p ≠ u → p ≠ v →
                H'.neighborSet p = H.neighborSet p := by
              intro p hpx hpu hpv
              ext w
              simp only [SimpleGraph.neighborSet]
              constructor
              · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                  ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                · exact h1
                · exact absurd hcontra hpu
                · exact absurd hcontra2 hpx
                · exact absurd hcontra3 hpv
                · exact absurd hcontra4 hpx
              · intro h1
                refine Or.inl ⟨h1, ?_⟩
                rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩)
                · exact hpu hcontra
                · exact hpv hcontra2
            have hmem_ux : u ∉ H.neighborSet x := hnux
            have hmem_vx : v ∉ H.neighborSet x := hnad
            have hmem_xu : x ∉ H.neighborSet u := hnux'
            have hmem_vu : v ∈ H.neighborSet u := H.adj_symm huv
            have hmem_xv : x ∉ H.neighborSet v := hnvu
            have hmem_uv : u ∈ H.neighborSet v := huv
            have hmem_v2 : v ∉ insert u (H.neighborSet x) := by
              simp only [Set.mem_insert_iff, not_or]
              exact ⟨hvu_ne, hmem_vx⟩
            have hcard_x : (H'.neighborSet x).ncard =
                (H.neighborSet x).ncard + 2 := by
              rw [heq_x]
              have h1 := Set.ncard_insert_of_notMem hmem_v2
              have h2 := Set.ncard_insert_of_notMem hmem_ux
              omega
            have hcard_u : (H'.neighborSet u).ncard =
                (H.neighborSet u).ncard := by
              rw [heq_u]
              exact Set.ncard_exchange hmem_xu hmem_vu
            have hcard_v : (H'.neighborSet v).ncard =
                (H.neighborSet v).ncard := by
              rw [heq_v]
              exact Set.ncard_exchange hmem_xv hmem_uv
            have hcard_o : ∀ p : V, p ≠ x → p ≠ u → p ≠ v →
                (H'.neighborSet p).ncard =
                (H.neighborSet p).ncard := by
              intro p hpx hpu hpv
              rw [heq_o p hpx hpu hpv]
            have hH'le : ∀ w, (H'.neighborSet w).ncard ≤ d w := by
              intro w
              by_cases hwx : w = x
              · rw [hwx]
                have hle_x := hHle x
                omega
              · by_cases hwu : w = u
                · rw [hwu]
                  have hle_u := hHle u
                  omega
                · by_cases hwv : w = v
                  · rw [hwv]
                    have hle_v := hHle v
                    omega
                  · have h := hcard_o w hwx hwu hwv
                    have hle := hHle w
                    omega
            have hH'mem : H' ∈ Smax := by
              rw [hSmax, Finset.mem_filter]
              exact ⟨Finset.mem_univ _, hH'le⟩
            have hx_inc : (H.neighborSet x).ncard + 1 ≤
                (H'.neighborSet x).ncard := by
              omega
            have hrest : ∀ w : V, w ≠ x →
                (H.neighborSet w).ncard ≤
                (H'.neighborSet w).ncard := by
              intro w hwx
              by_cases hwu : w = u
              · rw [hwu]
                omega
              · by_cases hwv : w = v
                · rw [hwv]
                  omega
                · have h := hcard_o w hwx hwu hwv
                  omega
            have hlt := cmp0 H' hH'le x hx_inc hrest
            have hle := hHmax H' hH'mem
            omega
        -- After C1, every u from (L) lies outside T.
        have hL_out : ∀ v : V, v ∈ T → v ≠ x → ∀ u : V,
            H.Adj v u → u ≠ x → ¬ H.Adj x u → u ∉ T := by
          intro v hvT hvx u huv hux_ne hnux huT
          have hadj : H.Adj x u := hC1 u huT hux_ne
          exact hnux hadj
        -- C2: for w outside T, |N(w) ∩ T| >= min (d w) r.
        have hC2 : ∀ w : V, w ∉ T →
            min (d w) r ≤ (H.neighborSet w ∩ ↑T).ncard := by
          intro w hwT
          by_contra hcon
          have hlt : (H.neighborSet w ∩ ↑T).ncard < min (d w) r :=
            not_le.mp hcon
          have hw_ne_x : w ≠ x := by
            intro hcon2
            rw [hcon2] at hwT
            exact hwT hxT
          have hxw_ne : x ≠ w := fun h => hw_ne_x h.symm
          by_cases hdeg : (H.neighborSet w).ncard < min (d w) r
          · -- Case (i): deg w < min, so w is deficient.
            have hw_def : (H.neighborSet w).ncard < d w :=
              lt_of_lt_of_le hdeg (min_le_left _ _)
            have hadj_xw : H.Adj x w := hC0 w hw_ne_x hw_def
            have hmem_xw : x ∈ H.neighborSet w :=
              H.adj_symm hadj_xw
            have hdeg_pos : 1 ≤ (H.neighborSet w).ncard := by
              have hsub : ({x} : Set V) ⊆ H.neighborSet w := by
                intro v hv
                simp only [Set.mem_singleton_iff] at hv
                rw [hv]
                exact hmem_xw
              have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
              simp only [Set.ncard_singleton] at hle
              exact hle
            have hdeg_lt_r : (H.neighborSet w).ncard < r :=
              lt_of_lt_of_le hdeg (min_le_right _ _)
            have hcard_erase : (T.erase x).card = r - 1 := by
              rw [hr]
              exact Finset.card_erase_of_mem hxT
            have hsub_diff : H.neighborSet w ∩ ↑(T.erase x) ⊆
                (H.neighborSet w) \ {x} := by
              intro v hv
              simp only [Set.mem_inter_iff, Set.mem_sdiff,
                Set.mem_singleton_iff] at hv ⊢
              constructor
              · exact hv.1
              · intro heq
                rw [heq] at hv
                have hmem : x ∈ (↑(T.erase x) : Set V) := hv.2
                rw [Finset.coe_erase, Set.mem_sdiff,
                  Set.mem_singleton_iff] at hmem
                exact hmem.2 rfl
            have hle_diff := Set.ncard_le_ncard hsub_diff
              (Set.toFinite _)
            have hdiff_eq : ((H.neighborSet w) \ {x}).ncard =
                (H.neighborSet w).ncard - 1 :=
              Set.ncard_sdiff_singleton_of_mem hmem_xw
            have hinter_lt : (H.neighborSet w ∩ ↑(T.erase x)).ncard <
                (T.erase x).card := by
              omega
            have hcard_lt : ((H.neighborSet w ∩ ↑(T.erase x)).toFinset).card <
                (T.erase x).card := by
              have heq := Set.ncard_eq_toFinset_card'
                (H.neighborSet w ∩ ↑(T.erase x))
              omega
            obtain ⟨v, hvt, hvs⟩ :=
              Finset.exists_mem_notMem_of_card_lt_card hcard_lt
            have hv_notmem :
                v ∉ H.neighborSet w ∩ ↑(T.erase x) := fun h =>
              hvs (Set.mem_toFinset.mpr h)
            obtain ⟨hvx_ne, hvT⟩ := Finset.mem_erase.mp hvt
            have hvT_coe : v ∈ (↑(T.erase x) : Set V) :=
              Finset.mem_coe.mpr hvt
            have hnadj : ¬ H.Adj w v := by
              intro hadj
              have hmem : v ∈ H.neighborSet w ∩ ↑(T.erase x) :=
                ⟨hadj, hvT_coe⟩
              exact hv_notmem hmem
            have hsatv : (H.neighborSet v).ncard = d v :=
              hTsat v hvT hvx_ne
            have hdxv : d x ≤ d v := hTdx v hvT
            obtain ⟨u, huv, hux_ne, hnux⟩ := hL v hvx_ne hsatv hdxv
            have hnvw : ¬ H.Adj v w :=
              fun h => hnadj (H.adj_symm h)
            have huw_ne : u ≠ w := by
              intro hcon2
              rw [hcon2] at huv
              exact hnvw huv
            have hvu_ne : v ≠ u := H.ne_of_adj huv
            have huv_ne : u ≠ v := fun h => hvu_ne h.symm
            have hxu_ne : x ≠ u := fun h => hux_ne h.symm
            have hxv_ne : x ≠ v := fun h => hvx_ne h.symm
            have hvw_ne : v ≠ w := by
              intro hcon2
              rw [hcon2] at hvT
              exact hwT hvT
            have hwv_ne : w ≠ v := fun h => hvw_ne h.symm
            have hwu_ne : w ≠ u := fun h => huw_ne h.symm
            have hnux' : ¬ H.Adj u x :=
              fun h => hnux (H.adj_symm h)
            have hadj_xv : H.Adj x v := hC1 v hvT hvx_ne
            -- Move: remove uv, add vw and ux. x and w rise by 1.
            let H' : SimpleGraph V :=
              { Adj := fun a b =>
                  (H.Adj a b ∧
                    ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∨
                  ((a = u ∧ b = x) ∨ (a = x ∧ b = u) ∨
                    (a = v ∧ b = w) ∨ (a = w ∧ b = v))
                symm := ⟨by
                  intro a b h
                  rcases h with ⟨h1, h2⟩ | h1
                  · refine Or.inl ⟨H.adj_symm h1, ?_⟩
                    intro hcon
                    apply h2
                    rcases hcon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact Or.inr ⟨rfl, rfl⟩
                    · exact Or.inl ⟨rfl, rfl⟩
                  · rcases h1 with
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                    · exact Or.inr
                        (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
                    · exact Or.inr
                        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
                loopless := ⟨by
                  intro a h
                  rcases h with ⟨h1, _⟩ | h1
                  · exact H.ne_of_adj h1 rfl
                  · rcases h1 with
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact hux_ne rfl
                    · exact hux_ne rfl.symm
                    · exact hvw_ne rfl
                    · exact hvw_ne rfl.symm⟩ }
            have heq_x : H'.neighborSet x =
                insert u (H.neighborSet x) := by
              ext t
              simp only [SimpleGraph.neighborSet, Set.mem_insert_iff]
              constructor
              · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨_, rfl⟩ |
                  ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                · exact Or.inr h1
                · exact absurd hcontra hxu_ne
                · exact Or.inl rfl
                · exact absurd hcontra2 hxv_ne
                · exact absurd hcontra3 hxw_ne
              · rintro (rfl | h1)
                · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                · refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩)
                  · exact hxu_ne hcontra
                  · exact hxv_ne hcontra2
            have heq_w : H'.neighborSet w =
                insert v (H.neighborSet w) := by
              ext t
              simp only [SimpleGraph.neighborSet, Set.mem_insert_iff]
              constructor
              · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                  ⟨hcontra3, _⟩ | ⟨_, rfl⟩)
                · exact Or.inr h1
                · exact absurd hcontra hwu_ne
                · exact absurd hcontra2 hw_ne_x
                · exact absurd hcontra3 hwv_ne
                · exact Or.inl rfl
              · rintro (rfl | h1)
                · exact Or.inr
                    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
                · refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩)
                  · exact hwu_ne hcontra
                  · exact hwv_ne hcontra2
            have heq_u : H'.neighborSet u =
                insert x ((H.neighborSet u) \ {v}) := by
              ext t
              simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                Set.mem_sdiff, Set.mem_singleton_iff]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨_, rfl⟩ | ⟨hcontra, _⟩ |
                  ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                · by_cases heq : t = v
                  · subst heq
                    exact absurd (Or.inl ⟨rfl, rfl⟩) h2
                  · exact Or.inr ⟨h1, heq⟩
                · exact Or.inl rfl
                · exact absurd hcontra hux_ne
                · exact absurd hcontra2 huv_ne
                · exact absurd hcontra3 huw_ne
              · rintro (rfl | ⟨h1, hne⟩)
                · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                · refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨_, heq⟩ | ⟨hcontra, _⟩)
                  · exact hne heq
                  · exact huv_ne hcontra
            have heq_v : H'.neighborSet v =
                insert w ((H.neighborSet v) \ {u}) := by
              ext t
              simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                Set.mem_sdiff, Set.mem_singleton_iff]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                  ⟨_, rfl⟩ | ⟨hcontra3, _⟩)
                · by_cases heq : t = u
                  · subst heq
                    exact absurd (Or.inr ⟨rfl, rfl⟩) h2
                  · exact Or.inr ⟨h1, heq⟩
                · exact absurd hcontra hvu_ne
                · exact absurd hcontra2 hvx_ne
                · exact Or.inl rfl
                · exact absurd hcontra3 hvw_ne
              · rintro (rfl | ⟨h1, hne⟩)
                · exact Or.inr
                    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
                · refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨_, heq⟩)
                  · exact hvu_ne hcontra
                  · exact hne heq
            have heq_o : ∀ p : V, p ≠ x → p ≠ w → p ≠ u →
                p ≠ v → H'.neighborSet p = H.neighborSet p := by
              intro p hpx hpw hpu hpv
              ext t
              simp only [SimpleGraph.neighborSet]
              constructor
              · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                  ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                · exact h1
                · exact absurd hcontra hpu
                · exact absurd hcontra2 hpx
                · exact absurd hcontra3 hpv
                · exact absurd hcontra4 hpw
              · intro h1
                refine Or.inl ⟨h1, ?_⟩
                rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩)
                · exact hpu hcontra
                · exact hpv hcontra2
            have hmem_ux : u ∉ H.neighborSet x := hnux
            have hmem_vw : v ∉ H.neighborSet w := hnadj
            have hmem_xu : x ∉ H.neighborSet u := hnux'
            have hmem_vu : v ∈ H.neighborSet u := H.adj_symm huv
            have hmem_wv : w ∉ H.neighborSet v := hnvw
            have hmem_uv : u ∈ H.neighborSet v := huv
            have hcard_x : (H'.neighborSet x).ncard =
                (H.neighborSet x).ncard + 1 := by
              rw [heq_x, Set.ncard_insert_of_notMem hmem_ux]
            have hcard_w : (H'.neighborSet w).ncard =
                (H.neighborSet w).ncard + 1 := by
              rw [heq_w, Set.ncard_insert_of_notMem hmem_vw]
            have hcard_u : (H'.neighborSet u).ncard =
                (H.neighborSet u).ncard := by
              rw [heq_u]
              exact Set.ncard_exchange hmem_xu hmem_vu
            have hcard_v : (H'.neighborSet v).ncard =
                (H.neighborSet v).ncard := by
              rw [heq_v]
              exact Set.ncard_exchange hmem_wv hmem_uv
            have hcard_o : ∀ p : V, p ≠ x → p ≠ w → p ≠ u →
                p ≠ v → (H'.neighborSet p).ncard =
                (H.neighborSet p).ncard := by
              intro p hpx hpw hpu hpv
              rw [heq_o p hpx hpw hpu hpv]
            have hH'le : ∀ p, (H'.neighborSet p).ncard ≤ d p := by
              intro p
              by_cases hpx : p = x
              · rw [hpx]
                have hle_x := hHle x
                omega
              · by_cases hpw : p = w
                · rw [hpw]
                  have hle_w := hHle w
                  omega
                · by_cases hpu : p = u
                  · rw [hpu]
                    have hle_u := hHle u
                    omega
                  · by_cases hpv : p = v
                    · rw [hpv]
                      have hle_v := hHle v
                      omega
                    · have h := hcard_o p hpx hpw hpu hpv
                      have hle := hHle p
                      omega
            have hH'mem : H' ∈ Smax := by
              rw [hSmax, Finset.mem_filter]
              exact ⟨Finset.mem_univ _, hH'le⟩
            have hx_inc : (H.neighborSet x).ncard + 1 ≤
                (H'.neighborSet x).ncard := by
              omega
            have hrest : ∀ p : V, p ≠ x →
                (H.neighborSet p).ncard ≤
                (H'.neighborSet p).ncard := by
              intro p hpx
              by_cases hpw : p = w
              · rw [hpw]
                omega
              · by_cases hpu : p = u
                · rw [hpu]
                  omega
                · by_cases hpv : p = v
                  · rw [hpv]
                    omega
                  · have h := hcard_o p hpx hpw hpu hpv
                    omega
            have hlt := cmp0 H' hH'le x hx_inc hrest
            have hle := hHmax H' hH'mem
            omega
          · -- Case (ii): deg w >= min > inter.
            have hge : min (d w) r ≤ (H.neighborSet w).ncard :=
              not_lt.mp hdeg
            have hlt_deg : (H.neighborSet w ∩ ↑T).ncard <
                (H.neighborSet w).ncard := by
              omega
            have hex_l : ∃ l, H.Adj w l ∧ l ∉ T := by
              by_contra hcon2
              have hsub : H.neighborSet w ⊆ ↑T := by
                intro l hl
                by_contra hlT
                have hlT' : l ∉ T :=
                  fun h => hlT (Finset.mem_coe.mpr h)
                exact hcon2 ⟨l, hl, hlT'⟩
              have heq : H.neighborSet w ∩ ↑T =
                  H.neighborSet w := by
                ext v
                simp only [Set.mem_inter_iff]
                constructor
                · intro h
                  exact h.1
                · intro h
                  exact ⟨h, hsub h⟩
              have hcard_eq : (H.neighborSet w ∩ ↑T).ncard =
                  (H.neighborSet w).ncard := by
                rw [heq]
              omega
            obtain ⟨l, hadj_wl, hlT⟩ := hex_l
            have hkey_l : key l < key x := hTout l hlT
            have hinter_lt_r : (H.neighborSet w ∩ ↑T).ncard < r := by
              have hmin_le : min (d w) r ≤ r := min_le_right _ _
              omega
            have hcard_lt2 :
                ((H.neighborSet w ∩ ↑T).toFinset).card <
                T.card := by
              have heq2 := Set.ncard_eq_toFinset_card'
                (H.neighborSet w ∩ ↑T)
              have hcard_T : T.card = r := hr.symm
              omega
            obtain ⟨v, hvT, hvs⟩ :=
              Finset.exists_mem_notMem_of_card_lt_card hcard_lt2
            have hv_notmem : v ∉ H.neighborSet w ∩ ↑T := fun h =>
              hvs (Set.mem_toFinset.mpr h)
            have hvT_coe : v ∈ (↑T : Set V) :=
              Finset.mem_coe.mpr hvT
            have hnadj_v : ¬ H.Adj w v := by
              intro hadj
              exact hv_notmem ⟨hadj, hvT_coe⟩
            by_cases heq_vx : v = x
            · -- v = x: remove wl, add xw.
              have hnadj_wx : ¬ H.Adj w x := by
                rw [← heq_vx]
                exact hnadj_v
              have hnxw : ¬ H.Adj x w :=
                fun h => hnadj_wx (H.adj_symm h)
              have hl_ne_x : l ≠ x := by
                intro hcon2
                rw [hcon2] at hlT
                exact hlT hxT
              have hxl_ne : x ≠ l := fun h => hl_ne_x h.symm
              have hw_ne_l : w ≠ l := H.ne_of_adj hadj_wl
              have hl_ne_w : l ≠ w := fun h => hw_ne_l h.symm
              let H' : SimpleGraph V :=
                { Adj := fun a b =>
                    (H.Adj a b ∧
                      ¬ ((a = w ∧ b = l) ∨ (a = l ∧ b = w))) ∨
                    ((a = x ∧ b = w) ∨ (a = w ∧ b = x))
                  symm := ⟨by
                    intro a b h
                    rcases h with ⟨h1, h2⟩ | h1
                    · refine Or.inl ⟨H.adj_symm h1, ?_⟩
                      intro hcon
                      apply h2
                      rcases hcon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                      · exact Or.inr ⟨rfl, rfl⟩
                      · exact Or.inl ⟨rfl, rfl⟩
                    · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
                      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
                  loopless := ⟨by
                    intro a h
                    rcases h with ⟨h1, _⟩ | h1
                    · exact H.ne_of_adj h1 rfl
                    · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                      · exact hxw_ne rfl
                      · exact hxw_ne rfl.symm⟩ }
              have heq_x : H'.neighborSet x =
                  insert w (H.neighborSet x) := by
                ext t
                simp only [SimpleGraph.neighborSet, Set.mem_insert_iff]
                constructor
                · rintro (⟨h1, _⟩ | ⟨_, rfl⟩ | ⟨hcontra, _⟩)
                  · exact Or.inr h1
                  · exact Or.inl rfl
                  · exact absurd hcontra hxw_ne
                · rintro (rfl | h1)
                  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                  · refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩)
                    · exact hxw_ne hcontra
                    · exact hxl_ne hcontra2
              have heq_l : H'.neighborSet l =
                  (H.neighborSet l) \ {w} := by
                ext t
                simp only [SimpleGraph.neighborSet,
                  Set.mem_sdiff, Set.mem_singleton_iff]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩)
                  · by_cases heq : t = w
                    · subst heq
                      exact absurd (Or.inr ⟨rfl, rfl⟩) h2
                    · exact ⟨h1, heq⟩
                  · exact absurd hcontra hl_ne_x
                  · exact absurd hcontra2 hl_ne_w
                · rintro ⟨h1, hne⟩
                  refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨_, heq⟩)
                  · exact hl_ne_w hcontra
                  · exact hne heq
              have heq_w : H'.neighborSet w =
                  insert x ((H.neighborSet w) \ {l}) := by
                ext t
                simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                  Set.mem_sdiff, Set.mem_singleton_iff]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨_, rfl⟩)
                  · by_cases heq : t = l
                    · subst heq
                      exact absurd (Or.inl ⟨rfl, rfl⟩) h2
                    · exact Or.inr ⟨h1, heq⟩
                  · exact absurd hcontra hw_ne_x
                  · exact Or.inl rfl
                · rintro (rfl | ⟨h1, hne⟩)
                  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
                  · refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨_, heq⟩ | ⟨hcontra, _⟩)
                    · exact hne heq
                    · exact hw_ne_l hcontra
              have heq_o : ∀ p : V, p ≠ x → p ≠ w → p ≠ l →
                  H'.neighborSet p = H.neighborSet p := by
                intro p hpx hpw hpl
                ext t
                simp only [SimpleGraph.neighborSet]
                constructor
                · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩)
                  · exact h1
                  · exact absurd hcontra hpx
                  · exact absurd hcontra2 hpw
                · intro h1
                  refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩)
                  · exact hpw hcontra
                  · exact hpl hcontra2
              have hmem_wx : w ∉ H.neighborSet x := hnxw
              have hmem_wl : w ∈ H.neighborSet l :=
                H.adj_symm hadj_wl
              have hmem_xw0 : x ∉ H.neighborSet w := hnadj_wx
              have hmem_lw : l ∈ H.neighborSet w := hadj_wl
              have hcard_x : (H'.neighborSet x).ncard =
                  (H.neighborSet x).ncard + 1 := by
                rw [heq_x, Set.ncard_insert_of_notMem hmem_wx]
              have hcard_l : (H'.neighborSet l).ncard + 1 =
                  (H.neighborSet l).ncard := by
                rw [heq_l]
                exact Set.ncard_sdiff_singleton_add_one hmem_wl
                  (Set.toFinite _)
              have hcard_w : (H'.neighborSet w).ncard =
                  (H.neighborSet w).ncard := by
                rw [heq_w]
                exact Set.ncard_exchange hmem_xw0 hmem_lw
              have hcard_o : ∀ p : V, p ≠ x → p ≠ w → p ≠ l →
                  (H'.neighborSet p).ncard =
                  (H.neighborSet p).ncard := by
                intro p hpx hpw hpl
                rw [heq_o p hpx hpw hpl]
              have hH'le : ∀ p, (H'.neighborSet p).ncard ≤ d p := by
                intro p
                by_cases hpx : p = x
                · rw [hpx]
                  have hle_x := hHle x
                  omega
                · by_cases hpw : p = w
                  · rw [hpw]
                    have hle_w := hHle w
                    omega
                  · by_cases hpl : p = l
                    · rw [hpl]
                      have hle_l := hHle l
                      omega
                    · have h := hcard_o p hpx hpw hpl
                      have hle := hHle p
                      omega
              have hH'mem : H' ∈ Smax := by
                rw [hSmax, Finset.mem_filter]
                exact ⟨Finset.mem_univ _, hH'le⟩
              have hx_inc : (H.neighborSet x).ncard + 1 ≤
                  (H'.neighborSet x).ncard := by
                omega
              have hl_le : (H.neighborSet l).ncard ≤
                  (H'.neighborSet l).ncard + 1 := by
                omega
              have hrest : ∀ p : V, p ≠ x → p ≠ l →
                  (H.neighborSet p).ncard ≤
                  (H'.neighborSet p).ncard := by
                intro p hpx hpl
                by_cases hpw : p = w
                · rw [hpw]
                  omega
                · have h := hcard_o p hpx hpw hpl
                  omega
              have hlt := cmp H' hH'le x l hkey_l hx_inc hl_le hrest
              have hle := hHmax H' hH'mem
              omega
            · -- v ≠ x: take u from (L), then split on u = l.
              have hvx_ne : v ≠ x := heq_vx
              have hsatv : (H.neighborSet v).ncard = d v :=
                hTsat v hvT hvx_ne
              have hdxv : d x ≤ d v := hTdx v hvT
              obtain ⟨u, huv, hux_ne, hnux⟩ := hL v hvx_ne hsatv hdxv
              have huT : u ∉ T :=
                hL_out v hvT hvx_ne u huv hux_ne hnux
              have hkey_u : key u < key x := hTout u huT
              have hnvw : ¬ H.Adj v w :=
                fun h => hnadj_v (H.adj_symm h)
              have huw_ne : u ≠ w := by
                intro hcon
                rw [hcon] at huv
                exact hnvw huv
              have hvu_ne : v ≠ u := H.ne_of_adj huv
              have huv_ne : u ≠ v := fun h => hvu_ne h.symm
              have hxu_ne : x ≠ u := fun h => hux_ne h.symm
              have hxv_ne : x ≠ v := fun h => hvx_ne h.symm
              have hl_ne_x : l ≠ x := by
                intro hcon2
                rw [hcon2] at hlT
                exact hlT hxT
              have hxl_ne : x ≠ l := fun h => hl_ne_x h.symm
              have hw_ne_l : w ≠ l := H.ne_of_adj hadj_wl
              have hl_ne_w : l ≠ w := fun h => hw_ne_l h.symm
              have hvw_ne : v ≠ w := by
                intro hcon2
                rw [hcon2] at hvT
                exact hwT hvT
              have hwv_ne : w ≠ v := fun h => hvw_ne h.symm
              have hvl_ne : v ≠ l := by
                intro hcon2
                rw [hcon2] at hvT
                exact hlT hvT
              have hlv_ne : l ≠ v := fun h => hvl_ne h.symm
              have hw_ne_x0 : w ≠ x := hw_ne_x
              have hnux' : ¬ H.Adj u x :=
                fun h => hnux (H.adj_symm h)
              by_cases hul : u = l
              · -- u = l: remove uv and wl (= wu), add vw and ux.
                have hwu_ne : w ≠ u := fun h => huw_ne h.symm
                have huy_ne : u ≠ w := huw_ne
                have hmem_wl0 : w ∈ H.neighborSet l :=
                  H.adj_symm hadj_wl
                have hmem_wu : w ∈ H.neighborSet u := by
                  rw [hul]
                  exact hmem_wl0
                let H' : SimpleGraph V :=
                  { Adj := fun a b =>
                      (H.Adj a b ∧
                        ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u) ∨
                          (a = w ∧ b = l) ∨ (a = l ∧ b = w))) ∨
                      ((a = u ∧ b = x) ∨ (a = x ∧ b = u) ∨
                        (a = v ∧ b = w) ∨ (a = w ∧ b = v))
                    symm := ⟨by
                      intro a b h
                      rcases h with ⟨h1, h2⟩ | h1
                      · refine Or.inl ⟨H.adj_symm h1, ?_⟩
                        intro hcon
                        apply h2
                        rcases hcon with
                          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                        · exact Or.inl ⟨rfl, rfl⟩
                        · exact Or.inr
                            (Or.inr (Or.inr ⟨rfl, rfl⟩))
                        · exact Or.inr
                            (Or.inr (Or.inl ⟨rfl, rfl⟩))
                      · rcases h1 with
                          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                        · exact Or.inr
                            (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
                        · exact Or.inr
                            (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
                    loopless := ⟨by
                      intro a h
                      rcases h with ⟨h1, _⟩ | h1
                      · exact H.ne_of_adj h1 rfl
                      · rcases h1 with
                          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact hux_ne rfl
                        · exact hux_ne rfl.symm
                        · exact hvw_ne rfl
                        · exact hvw_ne rfl.symm⟩ }
                have heq_x : H'.neighborSet x =
                    insert u (H.neighborSet x) := by
                  ext t
                  simp only [SimpleGraph.neighborSet, Set.mem_insert_iff]
                  constructor
                  · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨_, rfl⟩ |
                      ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                    · exact Or.inr h1
                    · exact absurd hcontra hxu_ne
                    · exact Or.inl rfl
                    · exact absurd hcontra2 hxv_ne
                    · exact absurd hcontra3 hxw_ne
                  · rintro (rfl | h1)
                    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                    · refine Or.inl ⟨h1, ?_⟩
                      rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                        ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                      · exact hxu_ne hcontra
                      · exact hxv_ne hcontra2
                      · exact hxw_ne hcontra3
                      · exact hxl_ne hcontra4
                have heq_v : H'.neighborSet v =
                    insert w ((H.neighborSet v) \ {u}) := by
                  ext t
                  simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                    Set.mem_sdiff, Set.mem_singleton_iff]
                  constructor
                  · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨_, rfl⟩ | ⟨hcontra3, _⟩)
                    · by_cases heq : t = u
                      · subst heq
                        exact absurd
                          (Or.inr (Or.inl ⟨rfl, rfl⟩)) h2
                      · exact Or.inr ⟨h1, heq⟩
                    · exact absurd hcontra hvu_ne
                    · exact absurd hcontra2 hvx_ne
                    · exact Or.inl rfl
                    · exact absurd hcontra3 hvw_ne
                  · rintro (rfl | ⟨h1, hne⟩)
                    · exact Or.inr
                        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
                    · refine Or.inl ⟨h1, ?_⟩
                      rintro (⟨hcontra, _⟩ | ⟨_, heq⟩ |
                        ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                      · exact hvu_ne hcontra
                      · exact hne heq
                      · exact hvw_ne hcontra2
                      · exact hvl_ne hcontra3
                have heq_w : H'.neighborSet w =
                    insert v ((H.neighborSet w) \ {l}) := by
                  ext t
                  simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                    Set.mem_sdiff, Set.mem_singleton_iff]
                  constructor
                  · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨hcontra3, _⟩ | ⟨_, rfl⟩)
                    · by_cases heq : t = l
                      · subst heq
                        exact absurd
                          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) h2
                      · exact Or.inr ⟨h1, heq⟩
                    · exact absurd hcontra hwu_ne
                    · exact absurd hcontra2 hw_ne_x0
                    · exact absurd hcontra3 hwv_ne
                    · exact Or.inl rfl
                  · rintro (rfl | ⟨h1, hne⟩)
                    · exact Or.inr
                        (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
                    · refine Or.inl ⟨h1, ?_⟩
                      rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                        ⟨_, heq⟩ | ⟨hcontra3, _⟩)
                      · exact hwu_ne hcontra
                      · exact hwv_ne hcontra2
                      · exact hne heq
                      · exact hw_ne_l hcontra3
                have heq_u : H'.neighborSet u =
                    insert x (((H.neighborSet u) \ {v}) \ {w}) := by
                  ext t
                  simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                    Set.mem_sdiff, Set.mem_singleton_iff]
                  constructor
                  · rintro (⟨h1, h2⟩ | ⟨_, rfl⟩ | ⟨hcontra, _⟩ |
                      ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                    · by_cases heq_v : t = v
                      · subst heq_v
                        exact absurd (Or.inl ⟨rfl, rfl⟩) h2
                      · by_cases heq_w : t = w
                        · subst heq_w
                          exact absurd
                            (Or.inr (Or.inr (Or.inr ⟨hul, rfl⟩))) h2
                        · exact Or.inr ⟨⟨h1, heq_v⟩, heq_w⟩
                    · exact Or.inl rfl
                    · exact absurd hcontra hux_ne
                    · exact absurd hcontra2 huv_ne
                    · exact absurd hcontra3 huw_ne
                  · rintro (rfl | ⟨⟨h1, hne_v⟩, hne_w⟩)
                    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                    · refine Or.inl ⟨h1, ?_⟩
                      rintro (⟨_, heq⟩ | ⟨hcontra, _⟩ |
                        ⟨hcontra2, _⟩ | ⟨_, heq2⟩)
                      · exact hne_v heq
                      · exact huv_ne hcontra
                      · exact huw_ne hcontra2
                      · exact hne_w heq2
                have heq_o : ∀ p : V, p ≠ x → p ≠ v → p ≠ w →
                    p ≠ u → p ≠ l →
                    H'.neighborSet p = H.neighborSet p := by
                  intro p hpx hpv hpw hpu hpl
                  ext t
                  simp only [SimpleGraph.neighborSet]
                  constructor
                  · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                    · exact h1
                    · exact absurd hcontra hpu
                    · exact absurd hcontra2 hpx
                    · exact absurd hcontra3 hpv
                    · exact absurd hcontra4 hpw
                  · intro h1
                    refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                    · exact hpu hcontra
                    · exact hpv hcontra2
                    · exact hpw hcontra3
                    · exact hpl hcontra4
                have hmem_ux : u ∉ H.neighborSet x := hnux
                have hmem_wv : w ∉ H.neighborSet v := hnvw
                have hmem_uv : u ∈ H.neighborSet v := huv
                have hmem_vw0 : v ∉ H.neighborSet w := hnadj_v
                have hmem_lw : l ∈ H.neighborSet w := hadj_wl
                have hmem_xu : x ∉ H.neighborSet u := hnux'
                have hmem_vu : v ∈ H.neighborSet u :=
                  H.adj_symm huv
                have hcard_x : (H'.neighborSet x).ncard =
                    (H.neighborSet x).ncard + 1 := by
                  rw [heq_x, Set.ncard_insert_of_notMem hmem_ux]
                have hcard_v : (H'.neighborSet v).ncard =
                    (H.neighborSet v).ncard := by
                  rw [heq_v]
                  exact Set.ncard_exchange hmem_wv hmem_uv
                have hcard_w : (H'.neighborSet w).ncard =
                    (H.neighborSet w).ncard := by
                  rw [heq_w]
                  exact Set.ncard_exchange hmem_vw0 hmem_lw
                have hcard_u : (H'.neighborSet u).ncard + 1 =
                    (H.neighborSet u).ncard := by
                  rw [heq_u]
                  have hmem_x2 :
                      x ∉ ((H.neighborSet u) \ {v}) \ {w} :=
                    fun h => hmem_xu h.1.1
                  have h1 := Set.ncard_insert_of_notMem hmem_x2
                  have hmem_w2 :
                      w ∈ (H.neighborSet u) \ {v} :=
                    ⟨hmem_wu, hwv_ne⟩
                  have h2 := Set.ncard_sdiff_singleton_add_one hmem_w2
                    (Set.toFinite _)
                  have h3 := Set.ncard_sdiff_singleton_add_one hmem_vu
                    (Set.toFinite _)
                  omega
                have hcard_o : ∀ p : V, p ≠ x → p ≠ v → p ≠ w →
                    p ≠ u → p ≠ l → (H'.neighborSet p).ncard =
                    (H.neighborSet p).ncard := by
                  intro p hpx hpv hpw hpu hpl
                  rw [heq_o p hpx hpv hpw hpu hpl]
                have hH'le : ∀ p, (H'.neighborSet p).ncard ≤ d p := by
                  intro p
                  by_cases hpx : p = x
                  · rw [hpx]
                    have hle_x := hHle x
                    omega
                  · by_cases hpv : p = v
                    · rw [hpv]
                      have hle_v := hHle v
                      omega
                    · by_cases hpw : p = w
                      · rw [hpw]
                        have hle_w := hHle w
                        omega
                      · by_cases hpu : p = u
                        · rw [hpu]
                          have hle_u := hHle u
                          omega
                        · have hpl : p ≠ l := fun h =>
                            hpu (h.trans hul.symm)
                          have h := hcard_o p hpx hpv hpw hpu hpl
                          have hle := hHle p
                          omega
                have hH'mem : H' ∈ Smax := by
                  rw [hSmax, Finset.mem_filter]
                  exact ⟨Finset.mem_univ _, hH'le⟩
                have hx_inc : (H.neighborSet x).ncard + 1 ≤
                    (H'.neighborSet x).ncard := by
                  omega
                have hu_le : (H.neighborSet u).ncard ≤
                    (H'.neighborSet u).ncard + 1 := by
                  omega
                have hrest : ∀ p : V, p ≠ x → p ≠ u →
                    (H.neighborSet p).ncard ≤
                    (H'.neighborSet p).ncard := by
                  intro p hpx hpu
                  by_cases hpv : p = v
                  · rw [hpv]
                    omega
                  · by_cases hpw : p = w
                    · rw [hpw]
                      omega
                    · have hpl : p ≠ l := fun h =>
                        hpu (h.trans hul.symm)
                      have h := hcard_o p hpx hpv hpw hpu hpl
                      omega
                have hlt := cmp H' hH'le x u hkey_u hx_inc hu_le hrest
                have hle := hHmax H' hH'mem
                omega
              · -- u ≠ l: remove uv and wl, add vw and ux.
                have hul_ne : u ≠ l := hul
                have hlu_ne : l ≠ u := fun h => hul h.symm
                have hwu_ne : w ≠ u := fun h => huw_ne h.symm
                have huy_ne : u ≠ w := huw_ne
                have hl_ne_u0 : l ≠ u := hlu_ne
                let H' : SimpleGraph V :=
                  { Adj := fun a b =>
                      (H.Adj a b ∧
                        ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u) ∨
                          (a = w ∧ b = l) ∨ (a = l ∧ b = w))) ∨
                      ((a = u ∧ b = x) ∨ (a = x ∧ b = u) ∨
                        (a = v ∧ b = w) ∨ (a = w ∧ b = v))
                    symm := ⟨by
                      intro a b h
                      rcases h with ⟨h1, h2⟩ | h1
                      · refine Or.inl ⟨H.adj_symm h1, ?_⟩
                        intro hcon
                        apply h2
                        rcases hcon with
                          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                        · exact Or.inl ⟨rfl, rfl⟩
                        · exact Or.inr
                            (Or.inr (Or.inr ⟨rfl, rfl⟩))
                        · exact Or.inr
                            (Or.inr (Or.inl ⟨rfl, rfl⟩))
                      · rcases h1 with
                          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                        · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                        · exact Or.inr
                            (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
                        · exact Or.inr
                            (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
                    loopless := ⟨by
                      intro a h
                      rcases h with ⟨h1, _⟩ | h1
                      · exact H.ne_of_adj h1 rfl
                      · rcases h1 with
                          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact hux_ne rfl
                        · exact hux_ne rfl.symm
                        · exact hvw_ne rfl
                        · exact hvw_ne rfl.symm⟩ }
                have heq_x : H'.neighborSet x =
                    insert u (H.neighborSet x) := by
                  ext t
                  simp only [SimpleGraph.neighborSet, Set.mem_insert_iff]
                  constructor
                  · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨_, rfl⟩ |
                      ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                    · exact Or.inr h1
                    · exact absurd hcontra hxu_ne
                    · exact Or.inl rfl
                    · exact absurd hcontra2 hxv_ne
                    · exact absurd hcontra3 hxw_ne
                  · rintro (rfl | h1)
                    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                    · refine Or.inl ⟨h1, ?_⟩
                      rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                        ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                      · exact hxu_ne hcontra
                      · exact hxv_ne hcontra2
                      · exact hxw_ne hcontra3
                      · exact hxl_ne hcontra4
                have heq_v : H'.neighborSet v =
                    insert w ((H.neighborSet v) \ {u}) := by
                  ext t
                  simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                    Set.mem_sdiff, Set.mem_singleton_iff]
                  constructor
                  · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨_, rfl⟩ | ⟨hcontra3, _⟩)
                    · by_cases heq : t = u
                      · subst heq
                        exact absurd
                          (Or.inr (Or.inl ⟨rfl, rfl⟩)) h2
                      · exact Or.inr ⟨h1, heq⟩
                    · exact absurd hcontra hvu_ne
                    · exact absurd hcontra2 hvx_ne
                    · exact Or.inl rfl
                    · exact absurd hcontra3 hvw_ne
                  · rintro (rfl | ⟨h1, hne⟩)
                    · exact Or.inr
                        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
                    · refine Or.inl ⟨h1, ?_⟩
                      rintro (⟨hcontra, _⟩ | ⟨_, heq⟩ |
                        ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                      · exact hvu_ne hcontra
                      · exact hne heq
                      · exact hvw_ne hcontra2
                      · exact hvl_ne hcontra3
                have heq_w : H'.neighborSet w =
                    insert v ((H.neighborSet w) \ {l}) := by
                  ext t
                  simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                    Set.mem_sdiff, Set.mem_singleton_iff]
                  constructor
                  · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨hcontra3, _⟩ | ⟨_, rfl⟩)
                    · by_cases heq : t = l
                      · subst heq
                        exact absurd
                          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) h2
                      · exact Or.inr ⟨h1, heq⟩
                    · exact absurd hcontra hwu_ne
                    · exact absurd hcontra2 hw_ne_x0
                    · exact absurd hcontra3 hwv_ne
                    · exact Or.inl rfl
                  · rintro (rfl | ⟨h1, hne⟩)
                    · exact Or.inr
                        (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
                    · refine Or.inl ⟨h1, ?_⟩
                      rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                        ⟨_, heq⟩ | ⟨hcontra3, _⟩)
                      · exact hwu_ne hcontra
                      · exact hwv_ne hcontra2
                      · exact hne heq
                      · exact hw_ne_l hcontra3
                have heq_u : H'.neighborSet u =
                    insert x ((H.neighborSet u) \ {v}) := by
                  ext t
                  simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                    Set.mem_sdiff, Set.mem_singleton_iff]
                  constructor
                  · rintro (⟨h1, h2⟩ | ⟨_, rfl⟩ | ⟨hcontra, _⟩ |
                      ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                    · by_cases heq : t = v
                      · subst heq
                        exact absurd (Or.inl ⟨rfl, rfl⟩) h2
                      · exact Or.inr ⟨h1, heq⟩
                    · exact Or.inl rfl
                    · exact absurd hcontra hux_ne
                    · exact absurd hcontra2 huv_ne
                    · exact absurd hcontra3 huy_ne
                  · rintro (rfl | ⟨h1, hne⟩)
                    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                    · refine Or.inl ⟨h1, ?_⟩
                      rintro (⟨_, heq⟩ | ⟨hcontra, _⟩ |
                        ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                      · exact hne heq
                      · exact huv_ne hcontra
                      · exact huw_ne hcontra2
                      · exact hul_ne hcontra3
                have heq_l : H'.neighborSet l =
                    (H.neighborSet l) \ {w} := by
                  ext t
                  simp only [SimpleGraph.neighborSet,
                    Set.mem_sdiff, Set.mem_singleton_iff]
                  constructor
                  · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                    · by_cases heq : t = w
                      · subst heq
                        exact absurd
                          (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) h2
                      · exact ⟨h1, heq⟩
                    · exact absurd hcontra hlu_ne
                    · exact absurd hcontra2 hl_ne_x
                    · exact absurd hcontra3 hlv_ne
                    · exact absurd hcontra4 hl_ne_w
                  · rintro ⟨h1, hne⟩
                    refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨hcontra3, _⟩ | ⟨_, heq⟩)
                    · exact hlu_ne hcontra
                    · exact hlv_ne hcontra2
                    · exact hl_ne_w hcontra3
                    · exact hne heq
                have heq_o : ∀ p : V, p ≠ x → p ≠ v → p ≠ w →
                    p ≠ u → p ≠ l →
                    H'.neighborSet p = H.neighborSet p := by
                  intro p hpx hpv hpw hpu hpl
                  ext t
                  simp only [SimpleGraph.neighborSet]
                  constructor
                  · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                    · exact h1
                    · exact absurd hcontra hpu
                    · exact absurd hcontra2 hpx
                    · exact absurd hcontra3 hpv
                    · exact absurd hcontra4 hpw
                  · intro h1
                    refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                    · exact hpu hcontra
                    · exact hpv hcontra2
                    · exact hpw hcontra3
                    · exact hpl hcontra4
                have hmem_ux : u ∉ H.neighborSet x := hnux
                have hmem_wv : w ∉ H.neighborSet v := hnvw
                have hmem_uv : u ∈ H.neighborSet v := huv
                have hmem_vw0 : v ∉ H.neighborSet w := hnadj_v
                have hmem_lw : l ∈ H.neighborSet w := hadj_wl
                have hmem_xu : x ∉ H.neighborSet u := hnux'
                have hmem_vu : v ∈ H.neighborSet u :=
                  H.adj_symm huv
                have hmem_wl : w ∈ H.neighborSet l :=
                  H.adj_symm hadj_wl
                have hcard_x : (H'.neighborSet x).ncard =
                    (H.neighborSet x).ncard + 1 := by
                  rw [heq_x, Set.ncard_insert_of_notMem hmem_ux]
                have hcard_v : (H'.neighborSet v).ncard =
                    (H.neighborSet v).ncard := by
                  rw [heq_v]
                  exact Set.ncard_exchange hmem_wv hmem_uv
                have hcard_w : (H'.neighborSet w).ncard =
                    (H.neighborSet w).ncard := by
                  rw [heq_w]
                  exact Set.ncard_exchange hmem_vw0 hmem_lw
                have hcard_u : (H'.neighborSet u).ncard =
                    (H.neighborSet u).ncard := by
                  rw [heq_u]
                  exact Set.ncard_exchange hmem_xu hmem_vu
                have hcard_l : (H'.neighborSet l).ncard + 1 =
                    (H.neighborSet l).ncard := by
                  rw [heq_l]
                  exact Set.ncard_sdiff_singleton_add_one hmem_wl
                    (Set.toFinite _)
                have hcard_o : ∀ p : V, p ≠ x → p ≠ v → p ≠ w →
                    p ≠ u → p ≠ l → (H'.neighborSet p).ncard =
                    (H.neighborSet p).ncard := by
                  intro p hpx hpv hpw hpu hpl
                  rw [heq_o p hpx hpv hpw hpu hpl]
                have hH'le : ∀ p, (H'.neighborSet p).ncard ≤ d p := by
                  intro p
                  by_cases hpx : p = x
                  · rw [hpx]
                    have hle_x := hHle x
                    omega
                  · by_cases hpv : p = v
                    · rw [hpv]
                      have hle_v := hHle v
                      omega
                    · by_cases hpw : p = w
                      · rw [hpw]
                        have hle_w := hHle w
                        omega
                      · by_cases hpu : p = u
                        · rw [hpu]
                          have hle_u := hHle u
                          omega
                        · by_cases hpl : p = l
                          · rw [hpl]
                            have hle_l := hHle l
                            omega
                          · have h := hcard_o p hpx hpv hpw hpu hpl
                            have hle := hHle p
                            omega
                have hH'mem : H' ∈ Smax := by
                  rw [hSmax, Finset.mem_filter]
                  exact ⟨Finset.mem_univ _, hH'le⟩
                have hx_inc : (H.neighborSet x).ncard + 1 ≤
                    (H'.neighborSet x).ncard := by
                  omega
                have hl_le : (H.neighborSet l).ncard ≤
                    (H'.neighborSet l).ncard + 1 := by
                  omega
                have hrest : ∀ p : V, p ≠ x → p ≠ l →
                    (H.neighborSet p).ncard ≤
                    (H'.neighborSet p).ncard := by
                  intro p hpx hpl
                  by_cases hpv : p = v
                  · rw [hpv]
                    omega
                  · by_cases hpw : p = w
                    · rw [hpw]
                      omega
                    · by_cases hpu : p = u
                      · rw [hpu]
                        omega
                      · have h := hcard_o p hpx hpv hpw hpu hpl
                        omega
                have hlt := cmp H' hH'le x l hkey_l hx_inc hl_le hrest
                have hle := hHmax H' hH'mem
                omega
        -- C3: T is a clique.
        have hC3 : ∀ v : V, v ∈ T → ∀ v' : V, v' ∈ T →
            v ≠ v' → H.Adj v v' := by
          intro v hvT v' hvT' hne
          by_contra hnad
          have hvx_ne : v ≠ x := by
            intro hcon
            rw [hcon] at hne hnad
            have hv'x_ne : v' ≠ x := fun h => hne h.symm
            have hadj : H.Adj x v' := hC1 v' hvT' hv'x_ne
            exact hnad hadj
          have hv'x_ne : v' ≠ x := by
            intro hcon
            rw [hcon] at hne hnad
            have hadj : H.Adj x v := hC1 v hvT hne
            exact hnad (H.adj_symm hadj)
          have hsatv : (H.neighborSet v).ncard = d v :=
            hTsat v hvT hvx_ne
          have hdxv : d x ≤ d v := hTdx v hvT
          obtain ⟨u, huv, hux_ne, hnux⟩ := hL v hvx_ne hsatv hdxv
          have hvu_ne : v ≠ u := H.ne_of_adj huv
          have huv_ne : u ≠ v := fun h => hvu_ne h.symm
          have hxu_ne : x ≠ u := fun h => hux_ne h.symm
          have hxv_ne : x ≠ v := fun h => hvx_ne h.symm
          have hxv'_ne : x ≠ v' := fun h => hv'x_ne h.symm
          have huT : u ∉ T :=
            hL_out v hvT hvx_ne u huv hux_ne hnux
          have hkey_u : key u < key x := hTout u huT
          have hnux' : ¬ H.Adj u x :=
            fun h => hnux (H.adj_symm h)
          by_cases hadj_uv' : H.Adj u v'
          · -- u adjacent to v': remove uv and uv', add vv' and ux.
            have huv'_ne : u ≠ v' := H.ne_of_adj hadj_uv'
            have hv'u_ne : v' ≠ u := fun h => huv'_ne h.symm
            have hne_sym : v' ≠ v := fun h => hne h.symm
            have hnvv : ¬ H.Adj v' v :=
              fun h => hnad (H.adj_symm h)
            have hmem_vu0 : v ∈ H.neighborSet u :=
              H.adj_symm huv
            have hmem_v'u : v' ∈ H.neighborSet u := hadj_uv'
            have hmem_uv0 : u ∈ H.neighborSet v := huv
            have hmem_uv'0 : u ∈ H.neighborSet v' :=
              H.adj_symm hadj_uv'
            let H' : SimpleGraph V :=
              { Adj := fun a b =>
                  (H.Adj a b ∧
                    ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u) ∨
                      (a = u ∧ b = v') ∨ (a = v' ∧ b = u))) ∨
                  ((a = v ∧ b = v') ∨ (a = v' ∧ b = v) ∨
                    (a = u ∧ b = x) ∨ (a = x ∧ b = u))
                symm := ⟨by
                  intro a b h
                  rcases h with ⟨h1, h2⟩ | h1
                  · refine Or.inl ⟨H.adj_symm h1, ?_⟩
                    intro hcon
                    apply h2
                    rcases hcon with
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                    · exact Or.inl ⟨rfl, rfl⟩
                    · exact Or.inr
                        (Or.inr (Or.inr ⟨rfl, rfl⟩))
                    · exact Or.inr
                        (Or.inr (Or.inl ⟨rfl, rfl⟩))
                  · rcases h1 with
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                    · exact Or.inr
                        (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
                    · exact Or.inr
                        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))⟩
                loopless := ⟨by
                  intro a h
                  rcases h with ⟨h1, _⟩ | h1
                  · exact H.ne_of_adj h1 rfl
                  · rcases h1 with
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · exact hne rfl
                    · exact hne rfl.symm
                    · exact hux_ne rfl
                    · exact hux_ne rfl.symm⟩ }
            have heq_x : H'.neighborSet x =
                insert u (H.neighborSet x) := by
              ext t
              simp only [SimpleGraph.neighborSet, Set.mem_insert_iff]
              constructor
              · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                  ⟨hcontra3, _⟩ | ⟨_, rfl⟩)
                · exact Or.inr h1
                · exact absurd hcontra hxv_ne
                · exact absurd hcontra2 hxv'_ne
                · exact absurd hcontra3 hxu_ne
                · exact Or.inl rfl
              · rintro (rfl | h1)
                · exact Or.inr
                    (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
                · refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                  · exact hxu_ne hcontra
                  · exact hxv_ne hcontra2
                  · exact hxu_ne hcontra3
                  · exact hxv'_ne hcontra4
            have heq_u : H'.neighborSet u =
                insert x (((H.neighborSet u) \ {v}) \ {v'}) := by
              ext t
              simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                Set.mem_sdiff, Set.mem_singleton_iff]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                  ⟨_, rfl⟩ | ⟨hcontra3, _⟩)
                · by_cases heq_v : t = v
                  · subst heq_v
                    exact absurd (Or.inl ⟨rfl, rfl⟩) h2
                  · by_cases heq_v' : t = v'
                    · subst heq_v'
                      exact absurd
                        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) h2
                    · exact Or.inr ⟨⟨h1, heq_v⟩, heq_v'⟩
                · exact absurd hcontra huv_ne
                · exact absurd hcontra2 huv'_ne
                · exact Or.inl rfl
                · exact absurd hcontra3 hux_ne
              · rintro (rfl | ⟨⟨h1, hne_v⟩, hne_v'⟩)
                · exact Or.inr
                    (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
                · refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨_, heq⟩ | ⟨hcontra, _⟩ |
                    ⟨_, heq2⟩ | ⟨hcontra2, _⟩)
                  · exact hne_v heq
                  · exact huv_ne hcontra
                  · exact hne_v' heq2
                  · exact huv'_ne hcontra2
            have heq_v : H'.neighborSet v =
                insert v' ((H.neighborSet v) \ {u}) := by
              ext t
              simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                Set.mem_sdiff, Set.mem_singleton_iff]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨_, rfl⟩ | ⟨hcontra, _⟩ |
                  ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                · by_cases heq : t = u
                  · subst heq
                    exact absurd
                      (Or.inr (Or.inl ⟨rfl, rfl⟩)) h2
                  · exact Or.inr ⟨h1, heq⟩
                · exact Or.inl rfl
                · exact absurd hcontra hne
                · exact absurd hcontra2 hvu_ne
                · exact absurd hcontra3 hvx_ne
              · rintro (rfl | ⟨h1, hne_t⟩)
                · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                · refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨_, heq⟩ |
                    ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                  · exact hvu_ne hcontra
                  · exact hne_t heq
                  · exact hvu_ne hcontra2
                  · exact hne hcontra3
            have heq_v' : H'.neighborSet v' =
                insert v ((H.neighborSet v') \ {u}) := by
              ext t
              simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                Set.mem_sdiff, Set.mem_singleton_iff]
              constructor
              · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨_, rfl⟩ |
                  ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                · by_cases heq : t = u
                  · subst heq
                    exact absurd
                      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) h2
                  · exact Or.inr ⟨h1, heq⟩
                · exact absurd hcontra hne_sym
                · exact Or.inl rfl
                · exact absurd hcontra2 hv'u_ne
                · exact absurd hcontra3 hv'x_ne
              · rintro (rfl | ⟨h1, hne⟩)
                · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                · refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨hcontra3, _⟩ | ⟨_, heq⟩)
                  · exact hv'u_ne hcontra
                  · exact hne_sym hcontra2
                  · exact hv'u_ne hcontra3
                  · exact hne heq
            have heq_o : ∀ p : V, p ≠ x → p ≠ v → p ≠ v' →
                p ≠ u → H'.neighborSet p = H.neighborSet p := by
              intro p hpx hpv hpv' hpu
              ext t
              simp only [SimpleGraph.neighborSet]
              constructor
              · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                  ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                · exact h1
                · exact absurd hcontra hpv
                · exact absurd hcontra2 hpv'
                · exact absurd hcontra3 hpu
                · exact absurd hcontra4 hpx
              · intro h1
                refine Or.inl ⟨h1, ?_⟩
                rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                  ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                · exact hpu hcontra
                · exact hpv hcontra2
                · exact hpu hcontra3
                · exact hpv' hcontra4
            have hmem_ux : u ∉ H.neighborSet x := hnux
            have hmem_xu : x ∉ H.neighborSet u := hnux'
            have hmem_vv : v' ∉ H.neighborSet v := hnad
            have hmem_v'v : v ∉ H.neighborSet v' := hnvv
            have hcard_x : (H'.neighborSet x).ncard =
                (H.neighborSet x).ncard + 1 := by
              rw [heq_x, Set.ncard_insert_of_notMem hmem_ux]
            have hcard_u : (H'.neighborSet u).ncard + 1 =
                (H.neighborSet u).ncard := by
              rw [heq_u]
              have hmem_x2 :
                  x ∉ ((H.neighborSet u) \ {v}) \ {v'} :=
                fun h => hmem_xu h.1.1
              have h1 := Set.ncard_insert_of_notMem hmem_x2
              have hmem_v'2 :
                  v' ∈ (H.neighborSet u) \ {v} :=
                ⟨hmem_v'u, hne_sym⟩
              have h2 := Set.ncard_sdiff_singleton_add_one hmem_v'2
                (Set.toFinite _)
              have h3 := Set.ncard_sdiff_singleton_add_one hmem_vu0
                (Set.toFinite _)
              omega
            have hcard_v : (H'.neighborSet v).ncard =
                (H.neighborSet v).ncard := by
              rw [heq_v]
              exact Set.ncard_exchange hmem_vv hmem_uv0
            have hcard_v' : (H'.neighborSet v').ncard =
                (H.neighborSet v').ncard := by
              rw [heq_v']
              exact Set.ncard_exchange hmem_v'v hmem_uv'0
            have hcard_o : ∀ p : V, p ≠ x → p ≠ v → p ≠ v' →
                p ≠ u → (H'.neighborSet p).ncard =
                (H.neighborSet p).ncard := by
              intro p hpx hpv hpv' hpu
              rw [heq_o p hpx hpv hpv' hpu]
            have hH'le : ∀ p, (H'.neighborSet p).ncard ≤ d p := by
              intro p
              by_cases hpx : p = x
              · rw [hpx]
                have hle_x := hHle x
                omega
              · by_cases hpu : p = u
                · rw [hpu]
                  have hle_u := hHle u
                  omega
                · by_cases hpv : p = v
                  · rw [hpv]
                    have hle_v := hHle v
                    omega
                  · by_cases hpv' : p = v'
                    · rw [hpv']
                      have hle_v' := hHle v'
                      omega
                    · have h := hcard_o p hpx hpv hpv' hpu
                      have hle := hHle p
                      omega
            have hH'mem : H' ∈ Smax := by
              rw [hSmax, Finset.mem_filter]
              exact ⟨Finset.mem_univ _, hH'le⟩
            have hx_inc : (H.neighborSet x).ncard + 1 ≤
                (H'.neighborSet x).ncard := by
              omega
            have hu_le : (H.neighborSet u).ncard ≤
                (H'.neighborSet u).ncard + 1 := by
              omega
            have hrest : ∀ p : V, p ≠ x → p ≠ u →
                (H.neighborSet p).ncard ≤
                (H'.neighborSet p).ncard := by
              intro p hpx hpu
              by_cases hpv : p = v
              · rw [hpv]
                omega
              · by_cases hpv' : p = v'
                · rw [hpv']
                  omega
                · have h := hcard_o p hpx hpv hpv' hpu
                  omega
            have hlt := cmp H' hH'le x u hkey_u hx_inc hu_le hrest
            have hle := hHmax H' hH'mem
            omega
          · -- ¬ Adj u v': take w from (L) for v'.
            have hsatv' : (H.neighborSet v').ncard = d v' :=
              hTsat v' hvT' hv'x_ne
            have hdxv' : d x ≤ d v' := hTdx v' hvT'
            obtain ⟨w, hvw', hwx_ne, hnwx⟩ :=
              hL v' hv'x_ne hsatv' hdxv'
            have hwu_ne : w ≠ u := by
              intro hcon
              rw [hcon] at hvw'
              exact hadj_uv' (H.adj_symm hvw')
            have huw_ne2 : u ≠ w := fun h => hwu_ne h.symm
            have hwT : w ∉ T :=
              hL_out v' hvT' hv'x_ne w hvw' hwx_ne hnwx
            have huv'_ne : u ≠ v' := by
              intro hcon
              rw [hcon] at huT
              exact huT hvT'
            have hvw_ne2 : v ≠ w := by
              intro hcon
              rw [hcon] at hvT
              exact hwT hvT
            have hwv_ne2 : w ≠ v := fun h => hvw_ne2 h.symm
            have hvw'_ne : v' ≠ w := H.ne_of_adj hvw'
            have hwv'_ne : w ≠ v' := fun h => hvw'_ne h.symm
            have hxw_ne2 : x ≠ w := fun h => hwx_ne h.symm
            have hnwx' : ¬ H.Adj w x :=
              fun h => hnwx (H.adj_symm h)
            have heps : d x - (H.neighborSet x).ncard = 1 ∨
                2 ≤ d x - (H.neighborSet x).ncard := by
              omega
            rcases heps with heps1 | heps2
            · -- eps = 1: remove uv, wv' and xy, add vv', ux, wx.
              obtain ⟨y, hyne, hylt, hkey_y⟩ := hP heps1
              have hadj_xy : H.Adj x y := hC0 y hyne hylt
              have hyu_ne : y ≠ u := by
                intro hcon
                rw [hcon] at hadj_xy
                exact hnux hadj_xy
              have hyw_ne : y ≠ w := by
                intro hcon
                rw [hcon] at hadj_xy
                exact hnwx hadj_xy
              have hkey_v : key x ≤ key v := (hTmem v).mp hvT
              have hyv_ne : y ≠ v := by
                intro hcon
                have heq : key y = key v := congrArg key hcon
                omega
              have hkey_v' : key x ≤ key v' := (hTmem v').mp hvT'
              have hyv'_ne : y ≠ v' := by
                intro hcon
                have heq : key y = key v' := congrArg key hcon
                omega
              have hxy_ne : x ≠ y := fun h => hyne h.symm
              have huy_ne_y : u ≠ y := fun h => hyu_ne h.symm
              have hwy_ne_y : w ≠ y := fun h => hyw_ne h.symm
              have hvy_ne_y : v ≠ y := fun h => hyv_ne h.symm
              have hv'y_ne : v' ≠ y := fun h => hyv'_ne h.symm
              have hne_sym : v' ≠ v := fun h => hne h.symm
              have hnvv : ¬ H.Adj v' v :=
                fun h => hnad (H.adj_symm h)
              have hv'u_ne : v' ≠ u := fun h => huv'_ne h.symm
              have hmem_yx0 : y ∈ H.neighborSet x := hadj_xy
              have hmem_xy0 : x ∈ H.neighborSet y :=
                H.adj_symm hadj_xy
              let H' : SimpleGraph V :=
                { Adj := fun a b =>
                    (H.Adj a b ∧
                      ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u) ∨
                        (a = w ∧ b = v') ∨ (a = v' ∧ b = w) ∨
                        (a = x ∧ b = y) ∨ (a = y ∧ b = x))) ∨
                    ((a = v ∧ b = v') ∨ (a = v' ∧ b = v) ∨
                      (a = u ∧ b = x) ∨ (a = x ∧ b = u) ∨
                      (a = w ∧ b = x) ∨ (a = x ∧ b = w))
                  symm := ⟨by
                    intro a b h
                    rcases h with ⟨h1, h2⟩ | h1
                    · refine Or.inl ⟨H.adj_symm h1, ?_⟩
                      intro hcon
                      apply h2
                      rcases hcon with
                        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                      · exact Or.inl ⟨rfl, rfl⟩
                      · exact Or.inr
                          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
                      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                      · exact Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
                      · exact Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
                    · rcases h1 with
                        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                      · exact Or.inr
                          (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
                      · exact Or.inr
                          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
                      · exact Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
                      · exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩
                  loopless := ⟨by
                    intro a h
                    rcases h with ⟨h1, _⟩ | h1
                    · exact H.ne_of_adj h1 rfl
                    · rcases h1 with
                        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                      · exact hne rfl
                      · exact hne rfl.symm
                      · exact hux_ne rfl
                      · exact hux_ne rfl.symm
                      · exact hwx_ne rfl
                      · exact hwx_ne rfl.symm⟩ }
              have heq_x : H'.neighborSet x =
                  insert w (insert u ((H.neighborSet x) \ {y})) := by
                ext t
                simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                  Set.mem_sdiff, Set.mem_singleton_iff]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨hcontra3, _⟩ | ⟨_, rfl⟩ | ⟨hcontra4, _⟩ |
                    ⟨_, rfl⟩)
                  · by_cases heq : t = y
                    · subst heq
                      exact absurd
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))) h2
                    · exact Or.inr (Or.inr ⟨h1, heq⟩)
                  · exact absurd hcontra hxv_ne
                  · exact absurd hcontra2 hxv'_ne
                  · exact absurd hcontra3 hxu_ne
                  · exact Or.inr (Or.inl rfl)
                  · exact absurd hcontra4 hxw_ne2
                  · exact Or.inl rfl
                · rintro (rfl | rfl | ⟨h1, hne_t⟩)
                  · exact Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
                  · exact Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
                  · refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩ | ⟨_, heq⟩ |
                      ⟨hcontra5, _⟩)
                    · exact hxu_ne hcontra
                    · exact hxv_ne hcontra2
                    · exact hxw_ne2 hcontra3
                    · exact hxv'_ne hcontra4
                    · exact hne_t heq
                    · exact hxy_ne hcontra5
              have heq_y : H'.neighborSet y =
                  (H.neighborSet y) \ {x} := by
                ext t
                simp only [SimpleGraph.neighborSet,
                  Set.mem_sdiff, Set.mem_singleton_iff]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩ | ⟨hcontra5, _⟩ |
                    ⟨hcontra6, _⟩)
                  · by_cases heq : t = x
                    · subst heq
                      exact absurd
                        (Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))) h2
                    · exact ⟨h1, heq⟩
                  · exact absurd hcontra hyv_ne
                  · exact absurd hcontra2 hyv'_ne
                  · exact absurd hcontra3 hyu_ne
                  · exact absurd hcontra4 hyne
                  · exact absurd hcontra5 hyw_ne
                  · exact absurd hcontra6 hyne
                · rintro ⟨h1, hne_t⟩
                  refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩ | ⟨hcontra5, _⟩ |
                    ⟨_, heq⟩)
                  · exact hyu_ne hcontra
                  · exact hyv_ne hcontra2
                  · exact hyw_ne hcontra3
                  · exact hyv'_ne hcontra4
                  · exact hyne hcontra5
                  · exact hne_t heq
              have heq_u : H'.neighborSet u =
                  insert x ((H.neighborSet u) \ {v}) := by
                ext t
                simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                  Set.mem_sdiff, Set.mem_singleton_iff]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨_, rfl⟩ | ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩ |
                    ⟨hcontra5, _⟩)
                  · by_cases heq : t = v
                    · subst heq
                      exact absurd (Or.inl ⟨rfl, rfl⟩) h2
                    · exact Or.inr ⟨h1, heq⟩
                  · exact absurd hcontra huv_ne
                  · exact absurd hcontra2 huv'_ne
                  · exact Or.inl rfl
                  · exact absurd hcontra3 hux_ne
                  · exact absurd hcontra4 huw_ne2
                  · exact absurd hcontra5 hux_ne
                · rintro (rfl | ⟨h1, hne_t⟩)
                  · exact Or.inr
                      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
                  · refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨_, heq⟩ | ⟨hcontra, _⟩ |
                      ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩ |
                      ⟨hcontra4, _⟩ | ⟨hcontra5, _⟩)
                    · exact hne_t heq
                    · exact huv_ne hcontra
                    · exact huw_ne2 hcontra2
                    · exact huv'_ne hcontra3
                    · exact hux_ne hcontra4
                    · exact huy_ne_y hcontra5
              have heq_w : H'.neighborSet w =
                  insert x ((H.neighborSet w) \ {v'}) := by
                ext t
                simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                  Set.mem_sdiff, Set.mem_singleton_iff]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩ | ⟨_, rfl⟩ |
                    ⟨hcontra5, _⟩)
                  · by_cases heq : t = v'
                    · subst heq
                      exact absurd
                        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) h2
                    · exact Or.inr ⟨h1, heq⟩
                  · exact absurd hcontra hwv_ne2
                  · exact absurd hcontra2 hwv'_ne
                  · exact absurd hcontra3 hwu_ne
                  · exact absurd hcontra4 hwx_ne
                  · exact Or.inl rfl
                  · exact absurd hcontra5 hwx_ne
                · rintro (rfl | ⟨h1, hne_t⟩)
                  · exact Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
                  · refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨_, heq⟩ | ⟨hcontra3, _⟩ |
                      ⟨hcontra4, _⟩ | ⟨hcontra5, _⟩)
                    · exact hwu_ne hcontra
                    · exact hwv_ne2 hcontra2
                    · exact hne_t heq
                    · exact hwv'_ne hcontra3
                    · exact hwx_ne hcontra4
                    · exact hwy_ne_y hcontra5
              have heq_v : H'.neighborSet v =
                  insert v' ((H.neighborSet v) \ {u}) := by
                ext t
                simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                  Set.mem_sdiff, Set.mem_singleton_iff]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨_, rfl⟩ | ⟨hcontra, _⟩ |
                    ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩ |
                    ⟨hcontra5, _⟩)
                  · by_cases heq : t = u
                    · subst heq
                      exact absurd
                        (Or.inr (Or.inl ⟨rfl, rfl⟩)) h2
                    · exact Or.inr ⟨h1, heq⟩
                  · exact Or.inl rfl
                  · exact absurd hcontra hne
                  · exact absurd hcontra2 hvu_ne
                  · exact absurd hcontra3 hvx_ne
                  · exact absurd hcontra4 hvw_ne2
                  · exact absurd hcontra5 hvx_ne
                · rintro (rfl | ⟨h1, hne_t⟩)
                  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                  · refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨hcontra, _⟩ | ⟨_, heq⟩ |
                      ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩ |
                      ⟨hcontra4, _⟩ | ⟨hcontra5, _⟩)
                    · exact hvu_ne hcontra
                    · exact hne_t heq
                    · exact hvw_ne2 hcontra2
                    · exact hne hcontra3
                    · exact hvx_ne hcontra4
                    · exact hvy_ne_y hcontra5
              have heq_v' : H'.neighborSet v' =
                  insert v ((H.neighborSet v') \ {w}) := by
                ext t
                simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                  Set.mem_sdiff, Set.mem_singleton_iff]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨_, rfl⟩ |
                    ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩ |
                    ⟨hcontra5, _⟩)
                  · by_cases heq : t = w
                    · subst heq
                      exact absurd
                        (Or.inr
                          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))) h2
                    · exact Or.inr ⟨h1, heq⟩
                  · exact absurd hcontra hne_sym
                  · exact Or.inl rfl
                  · exact absurd hcontra2 hv'u_ne
                  · exact absurd hcontra3 hv'x_ne
                  · exact absurd hcontra4 hvw'_ne
                  · exact absurd hcontra5 hv'x_ne
                · rintro (rfl | ⟨h1, hne_t⟩)
                  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                  · refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨hcontra3, _⟩ | ⟨_, heq⟩ |
                      ⟨hcontra4, _⟩ | ⟨hcontra5, _⟩)
                    · exact hv'u_ne hcontra
                    · exact hne_sym hcontra2
                    · exact hvw'_ne hcontra3
                    · exact hne_t heq
                    · exact hv'x_ne hcontra4
                    · exact hv'y_ne hcontra5
              have heq_o : ∀ p : V, p ≠ x → p ≠ y → p ≠ v →
                  p ≠ v' → p ≠ u → p ≠ w →
                  H'.neighborSet p = H.neighborSet p := by
                intro p hpx hpy hpv hpv' hpu hpw
                ext t
                simp only [SimpleGraph.neighborSet]
                constructor
                · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩ | ⟨hcontra5, _⟩ |
                    ⟨hcontra6, _⟩)
                  · exact h1
                  · exact absurd hcontra hpv
                  · exact absurd hcontra2 hpv'
                  · exact absurd hcontra3 hpu
                  · exact absurd hcontra4 hpx
                  · exact absurd hcontra5 hpw
                  · exact absurd hcontra6 hpx
                · intro h1
                  refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩ |
                    ⟨hcontra5, _⟩ | ⟨hcontra6, _⟩)
                  · exact hpu hcontra
                  · exact hpv hcontra2
                  · exact hpw hcontra3
                  · exact hpv' hcontra4
                  · exact hpx hcontra5
                  · exact hpy hcontra6
              have hmem_ux : u ∉ H.neighborSet x := hnux
              have hmem_wx : w ∉ H.neighborSet x := hnwx
              have hmem_xu : x ∉ H.neighborSet u := hnux'
              have hmem_vu : v ∈ H.neighborSet u :=
                H.adj_symm huv
              have hmem_xw : x ∉ H.neighborSet w := hnwx'
              have hmem_v'w : v' ∈ H.neighborSet w :=
                H.adj_symm hvw'
              have hmem_vv : v' ∉ H.neighborSet v := hnad
              have hmem_uv : u ∈ H.neighborSet v := huv
              have hmem_v'v : v ∉ H.neighborSet v' := hnvv
              have hmem_wv' : w ∈ H.neighborSet v' := hvw'
              have hmem_u2 : u ∉ (H.neighborSet x) \ {y} :=
                fun h => hmem_ux h.1
              have hmem_w3 :
                  w ∉ insert u ((H.neighborSet x) \ {y}) := by
                simp only [Set.mem_insert_iff, not_or]
                constructor
                · exact hwu_ne
                · exact fun h => hmem_wx h.1
              have hcard_x : (H'.neighborSet x).ncard =
                  (H.neighborSet x).ncard + 1 := by
                rw [heq_x]
                have h1 := Set.ncard_insert_of_notMem hmem_w3
                have h2 := Set.ncard_insert_of_notMem hmem_u2
                have h3 := Set.ncard_sdiff_singleton_add_one hmem_yx0
                  (Set.toFinite _)
                omega
              have hcard_y : (H'.neighborSet y).ncard + 1 =
                  (H.neighborSet y).ncard := by
                rw [heq_y]
                exact Set.ncard_sdiff_singleton_add_one hmem_xy0
                  (Set.toFinite _)
              have hcard_u : (H'.neighborSet u).ncard =
                  (H.neighborSet u).ncard := by
                rw [heq_u]
                exact Set.ncard_exchange hmem_xu hmem_vu
              have hcard_w : (H'.neighborSet w).ncard =
                  (H.neighborSet w).ncard := by
                rw [heq_w]
                exact Set.ncard_exchange hmem_xw hmem_v'w
              have hcard_v : (H'.neighborSet v).ncard =
                  (H.neighborSet v).ncard := by
                rw [heq_v]
                exact Set.ncard_exchange hmem_vv hmem_uv
              have hcard_v' : (H'.neighborSet v').ncard =
                  (H.neighborSet v').ncard := by
                rw [heq_v']
                exact Set.ncard_exchange hmem_v'v hmem_wv'
              have hcard_o : ∀ p : V, p ≠ x → p ≠ y → p ≠ v →
                  p ≠ v' → p ≠ u → p ≠ w →
                  (H'.neighborSet p).ncard =
                  (H.neighborSet p).ncard := by
                intro p hpx hpy hpv hpv' hpu hpw
                rw [heq_o p hpx hpy hpv hpv' hpu hpw]
              have hH'le : ∀ p, (H'.neighborSet p).ncard ≤ d p := by
                intro p
                by_cases hpx : p = x
                · rw [hpx]
                  have hle_x := hHle x
                  omega
                · by_cases hpy : p = y
                  · rw [hpy]
                    have hle_y := hHle y
                    omega
                  · by_cases hpu : p = u
                    · rw [hpu]
                      have hle_u := hHle u
                      omega
                    · by_cases hpw : p = w
                      · rw [hpw]
                        have hle_w := hHle w
                        omega
                      · by_cases hpv : p = v
                        · rw [hpv]
                          have hle_v := hHle v
                          omega
                        · by_cases hpv' : p = v'
                          · rw [hpv']
                            have hle_v' := hHle v'
                            omega
                          · have h := hcard_o p hpx hpy hpv hpv' hpu hpw
                            have hle := hHle p
                            omega
              have hH'mem : H' ∈ Smax := by
                rw [hSmax, Finset.mem_filter]
                exact ⟨Finset.mem_univ _, hH'le⟩
              have hx_inc : (H.neighborSet x).ncard + 1 ≤
                  (H'.neighborSet x).ncard := by
                omega
              have hy_le : (H.neighborSet y).ncard ≤
                  (H'.neighborSet y).ncard + 1 := by
                omega
              have hrest : ∀ p : V, p ≠ x → p ≠ y →
                  (H.neighborSet p).ncard ≤
                  (H'.neighborSet p).ncard := by
                intro p hpx hpy
                by_cases hpu : p = u
                · rw [hpu]
                  omega
                · by_cases hpw : p = w
                  · rw [hpw]
                    omega
                  · by_cases hpv : p = v
                    · rw [hpv]
                      omega
                    · by_cases hpv' : p = v'
                      · rw [hpv']
                        omega
                      · have h := hcard_o p hpx hpy hpv hpv' hpu hpw
                        omega
              have hlt := cmp H' hH'le x y hkey_y hx_inc hy_le hrest
              have hle := hHmax H' hH'mem
              omega
            · -- eps >= 2: remove uv and wv', add vv', ux and wx.
              have hne_sym : v' ≠ v := fun h => hne h.symm
              have hnvv : ¬ H.Adj v' v :=
                fun h => hnad (H.adj_symm h)
              have hv'u_ne : v' ≠ u := fun h => huv'_ne h.symm
              have hvu_ne2 : v ≠ u := H.ne_of_adj huv
              have hnux'_u : ¬ H.Adj u x := hnux'
              have hmem_v'u_w : v' ∈ H.neighborSet w :=
                H.adj_symm hvw'
              let H' : SimpleGraph V :=
                { Adj := fun a b =>
                    (H.Adj a b ∧
                      ¬ ((a = u ∧ b = v) ∨ (a = v ∧ b = u) ∨
                        (a = w ∧ b = v') ∨ (a = v' ∧ b = w))) ∨
                    ((a = v ∧ b = v') ∨ (a = v' ∧ b = v) ∨
                      (a = u ∧ b = x) ∨ (a = x ∧ b = u) ∨
                      (a = w ∧ b = x) ∨ (a = x ∧ b = w))
                  symm := ⟨by
                    intro a b h
                    rcases h with ⟨h1, h2⟩ | h1
                    · refine Or.inl ⟨H.adj_symm h1, ?_⟩
                      intro hcon
                      apply h2
                      rcases hcon with
                        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                      · exact Or.inl ⟨rfl, rfl⟩
                      · exact Or.inr
                          (Or.inr (Or.inr ⟨rfl, rfl⟩))
                      · exact Or.inr
                          (Or.inr (Or.inl ⟨rfl, rfl⟩))
                    · rcases h1 with
                        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                      · exact Or.inr
                          (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
                      · exact Or.inr
                          (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
                      · exact Or.inr
                          (Or.inr
                            (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
                      · exact Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩
                  loopless := ⟨by
                    intro a h
                    rcases h with ⟨h1, _⟩ | h1
                    · exact H.ne_of_adj h1 rfl
                    · rcases h1 with
                        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                      · exact hne rfl
                      · exact hne rfl.symm
                      · exact hux_ne rfl
                      · exact hux_ne rfl.symm
                      · exact hwx_ne rfl
                      · exact hwx_ne rfl.symm⟩ }
              have heq_x : H'.neighborSet x =
                  insert w (insert u (H.neighborSet x)) := by
                ext t
                simp only [SimpleGraph.neighborSet, Set.mem_insert_iff]
                constructor
                · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨hcontra3, _⟩ | ⟨_, rfl⟩ | ⟨hcontra4, _⟩ |
                    ⟨_, rfl⟩)
                  · exact Or.inr (Or.inr h1)
                  · exact absurd hcontra hxv_ne
                  · exact absurd hcontra2 hxv'_ne
                  · exact absurd hcontra3 hxu_ne
                  · exact Or.inr (Or.inl rfl)
                  · exact absurd hcontra4 hxw_ne2
                  · exact Or.inl rfl
                · rintro (rfl | rfl | h1)
                  · exact Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))
                  · exact Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
                  · refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                    · exact hxu_ne hcontra
                    · exact hxv_ne hcontra2
                    · exact hxw_ne2 hcontra3
                    · exact hxv'_ne hcontra4
              have heq_u : H'.neighborSet u =
                  insert x ((H.neighborSet u) \ {v}) := by
                ext t
                simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                  Set.mem_sdiff, Set.mem_singleton_iff]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨_, rfl⟩ | ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩ |
                    ⟨hcontra5, _⟩)
                  · by_cases heq : t = v
                    · subst heq
                      exact absurd (Or.inl ⟨rfl, rfl⟩) h2
                    · exact Or.inr ⟨h1, heq⟩
                  · exact absurd hcontra huv_ne
                  · exact absurd hcontra2 huv'_ne
                  · exact Or.inl rfl
                  · exact absurd hcontra3 hux_ne
                  · exact absurd hcontra4 huw_ne2
                  · exact absurd hcontra5 hux_ne
                · rintro (rfl | ⟨h1, hne⟩)
                  · exact Or.inr
                      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
                  · refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨_, heq⟩ | ⟨hcontra, _⟩ |
                      ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                    · exact hne heq
                    · exact huv_ne hcontra
                    · exact huw_ne2 hcontra2
                    · exact huv'_ne hcontra3
              have heq_w : H'.neighborSet w =
                  insert x ((H.neighborSet w) \ {v'}) := by
                ext t
                simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                  Set.mem_sdiff, Set.mem_singleton_iff]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩ | ⟨_, rfl⟩ |
                    ⟨hcontra5, _⟩)
                  · by_cases heq : t = v'
                    · subst heq
                      exact absurd
                        (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) h2
                    · exact Or.inr ⟨h1, heq⟩
                  · exact absurd hcontra hwv_ne2
                  · exact absurd hcontra2 hwv'_ne
                  · exact absurd hcontra3 hwu_ne
                  · exact absurd hcontra4 hwx_ne
                  · exact Or.inl rfl
                  · exact absurd hcontra5 hwx_ne
                · rintro (rfl | ⟨h1, hne⟩)
                  · exact Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
                  · refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨_, heq⟩ | ⟨hcontra3, _⟩)
                    · exact hwu_ne hcontra
                    · exact hwv_ne2 hcontra2
                    · exact hne heq
                    · exact hwv'_ne hcontra3
              have heq_v : H'.neighborSet v =
                  insert v' ((H.neighborSet v) \ {u}) := by
                ext t
                simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                  Set.mem_sdiff, Set.mem_singleton_iff]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨_, rfl⟩ | ⟨hcontra, _⟩ |
                    ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩ |
                    ⟨hcontra5, _⟩)
                  · by_cases heq : t = u
                    · subst heq
                      exact absurd
                        (Or.inr (Or.inl ⟨rfl, rfl⟩)) h2
                    · exact Or.inr ⟨h1, heq⟩
                  · exact Or.inl rfl
                  · exact absurd hcontra hne
                  · exact absurd hcontra2 hvu_ne2
                  · exact absurd hcontra3 hvx_ne
                  · exact absurd hcontra4 hvw_ne2
                  · exact absurd hcontra5 hvx_ne
                · rintro (rfl | ⟨h1, hne_t⟩)
                  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
                  · refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨hcontra, _⟩ | ⟨_, heq⟩ |
                      ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩)
                    · exact hvu_ne2 hcontra
                    · exact hne_t heq
                    · exact hvw_ne2 hcontra2
                    · exact hne hcontra3
              have heq_v' : H'.neighborSet v' =
                  insert v ((H.neighborSet v') \ {w}) := by
                ext t
                simp only [SimpleGraph.neighborSet, Set.mem_insert_iff,
                  Set.mem_sdiff, Set.mem_singleton_iff]
                constructor
                · rintro (⟨h1, h2⟩ | ⟨hcontra, _⟩ | ⟨_, rfl⟩ |
                    ⟨hcontra2, _⟩ | ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩ |
                    ⟨hcontra5, _⟩)
                  · by_cases heq : t = w
                    · subst heq
                      exact absurd
                        (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) h2
                    · exact Or.inr ⟨h1, heq⟩
                  · exact absurd hcontra hne_sym
                  · exact Or.inl rfl
                  · exact absurd hcontra2 hv'u_ne
                  · exact absurd hcontra3 hv'x_ne
                  · exact absurd hcontra4 hvw'_ne
                  · exact absurd hcontra5 hv'x_ne
                · rintro (rfl | ⟨h1, hne_t⟩)
                  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
                  · refine Or.inl ⟨h1, ?_⟩
                    rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                      ⟨hcontra3, _⟩ | ⟨_, heq⟩)
                    · exact hv'u_ne hcontra
                    · exact hne_sym hcontra2
                    · exact hvw'_ne hcontra3
                    · exact hne_t heq
              have heq_o : ∀ p : V, p ≠ x → p ≠ v → p ≠ v' →
                  p ≠ u → p ≠ w →
                  H'.neighborSet p = H.neighborSet p := by
                intro p hpx hpv hpv' hpu hpw
                ext t
                simp only [SimpleGraph.neighborSet]
                constructor
                · rintro (⟨h1, _⟩ | ⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩ | ⟨hcontra5, _⟩ |
                    ⟨hcontra6, _⟩)
                  · exact h1
                  · exact absurd hcontra hpv
                  · exact absurd hcontra2 hpv'
                  · exact absurd hcontra3 hpu
                  · exact absurd hcontra4 hpx
                  · exact absurd hcontra5 hpw
                  · exact absurd hcontra6 hpx
                · intro h1
                  refine Or.inl ⟨h1, ?_⟩
                  rintro (⟨hcontra, _⟩ | ⟨hcontra2, _⟩ |
                    ⟨hcontra3, _⟩ | ⟨hcontra4, _⟩)
                  · exact hpu hcontra
                  · exact hpv hcontra2
                  · exact hpw hcontra3
                  · exact hpv' hcontra4
              have hmem_ux : u ∉ H.neighborSet x := hnux
              have hmem_wx : w ∉ H.neighborSet x := hnwx
              have hmem_xu : x ∉ H.neighborSet u := hnux'_u
              have hmem_vu : v ∈ H.neighborSet u :=
                H.adj_symm huv
              have hmem_xw : x ∉ H.neighborSet w := hnwx'
              have hmem_vv : v' ∉ H.neighborSet v := hnad
              have hmem_uv : u ∈ H.neighborSet v := huv
              have hmem_v'v : v ∉ H.neighborSet v' := hnvv
              have hmem_wv' : w ∈ H.neighborSet v' := hvw'
              have hmem_w2 : w ∉ insert u (H.neighborSet x) := by
                simp only [Set.mem_insert_iff, not_or]
                exact ⟨hwu_ne, hmem_wx⟩
              have hcard_x : (H'.neighborSet x).ncard =
                  (H.neighborSet x).ncard + 2 := by
                rw [heq_x]
                have h1 := Set.ncard_insert_of_notMem hmem_w2
                have h2 := Set.ncard_insert_of_notMem hmem_ux
                omega
              have hcard_u : (H'.neighborSet u).ncard =
                  (H.neighborSet u).ncard := by
                rw [heq_u]
                exact Set.ncard_exchange hmem_xu hmem_vu
              have hcard_w : (H'.neighborSet w).ncard =
                  (H.neighborSet w).ncard := by
                rw [heq_w]
                exact Set.ncard_exchange hmem_xw hmem_v'u_w
              have hcard_v : (H'.neighborSet v).ncard =
                  (H.neighborSet v).ncard := by
                rw [heq_v]
                exact Set.ncard_exchange hmem_vv hmem_uv
              have hcard_v' : (H'.neighborSet v').ncard =
                  (H.neighborSet v').ncard := by
                rw [heq_v']
                exact Set.ncard_exchange hmem_v'v hmem_wv'
              have hcard_o : ∀ p : V, p ≠ x → p ≠ v → p ≠ v' →
                  p ≠ u → p ≠ w → (H'.neighborSet p).ncard =
                  (H.neighborSet p).ncard := by
                intro p hpx hpv hpv' hpu hpw
                rw [heq_o p hpx hpv hpv' hpu hpw]
              have hH'le : ∀ p, (H'.neighborSet p).ncard ≤ d p := by
                intro p
                by_cases hpx : p = x
                · rw [hpx]
                  have hle_x := hHle x
                  omega
                · by_cases hpu : p = u
                  · rw [hpu]
                    have hle_u := hHle u
                    omega
                  · by_cases hpw : p = w
                    · rw [hpw]
                      have hle_w := hHle w
                      omega
                    · by_cases hpv : p = v
                      · rw [hpv]
                        have hle_v := hHle v
                        omega
                      · by_cases hpv' : p = v'
                        · rw [hpv']
                          have hle_v' := hHle v'
                          omega
                        · have h := hcard_o p hpx hpv hpv' hpu hpw
                          have hle := hHle p
                          omega
              have hH'mem : H' ∈ Smax := by
                rw [hSmax, Finset.mem_filter]
                exact ⟨Finset.mem_univ _, hH'le⟩
              have hx_inc : (H.neighborSet x).ncard + 1 ≤
                  (H'.neighborSet x).ncard := by
                omega
              have hrest : ∀ p : V, p ≠ x →
                  (H.neighborSet p).ncard ≤
                  (H'.neighborSet p).ncard := by
                intro p hpx
                by_cases hpu : p = u
                · rw [hpu]
                  omega
                · by_cases hpw : p = w
                  · rw [hpw]
                    omega
                  · by_cases hpv : p = v
                    · rw [hpv]
                      omega
                    · by_cases hpv' : p = v'
                      · rw [hpv']
                        omega
                      · have h := hcard_o p hpx hpv hpv' hpu hpw
                        omega
              have hlt := cmp0 H' hH'le x hx_inc hrest
              have hle := hHmax H' hH'mem
              omega
        -- Final contradiction: counting at S = T.
        have hsum_gap : ∑ v ∈ T, (d v - (H.neighborSet v).ncard) =
            d x - (H.neighborSet x).ncard := by
          apply Finset.sum_eq_single_of_mem x hxT
          · intro v hvT hvx_ne
            have hsat : (H.neighborSet v).ncard = d v :=
              hTsat v hvT hvx_ne
            omega
        have hsum_d : ∑ v ∈ T, d v =
            (∑ v ∈ T, (H.neighborSet v).ncard) +
            (d x - (H.neighborSet x).ncard) := by
          have heq : ∀ v ∈ T, d v =
              (H.neighborSet v).ncard + (d v - (H.neighborSet v).ncard) := by
            intro v _
            have hle := hHle v
            omega
          have hsum : ∑ v ∈ T, d v =
              ∑ v ∈ T, ((H.neighborSet v).ncard +
                (d v - (H.neighborSet v).ncard)) :=
            Finset.sum_congr rfl heq
          rw [hsum, Finset.sum_add_distrib, hsum_gap]
        have hcard_eq : ∀ v : V, (H.neighborFinset v).card =
            (H.neighborSet v).ncard := by
          intro v
          have h1 := SimpleGraph.card_neighborFinset_eq_degree
            (G := H) (v := v)
          have h2 := SimpleGraph.ncard_neighborSet (G := H) (v := v)
          omega
        have hsum_ncard_eq : ∑ v ∈ T, (H.neighborSet v).ncard =
            ∑ v ∈ T, (H.neighborFinset v).card :=
          Finset.sum_congr rfl (fun v _ => (hcard_eq v).symm)
        have hEg := hineq T
        rw [← hr] at hEg
        have hinside : ∀ v ∈ T,
            ((H.neighborFinset v).filter (· ∈ T)).card = r - 1 := by
          intro v hvT
          have heq : (H.neighborFinset v).filter (· ∈ T)
              = T.erase v := by
            ext w
            simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
              Finset.mem_erase]
            constructor
            · rintro ⟨hadj, hwT⟩
              exact ⟨fun h => H.ne_of_adj hadj h.symm, hwT⟩
            · rintro ⟨hne, hwT⟩
              have hne' : v ≠ w := fun h => hne h.symm
              exact ⟨hC3 v hvT w hwT hne', hwT⟩
          rw [heq, Finset.card_erase_of_mem hvT, ← hr]
        have hsplit : ∀ v ∈ T, (H.neighborFinset v).card
            = ((H.neighborFinset v).filter (· ∈ T)).card
              + ((H.neighborFinset v).filter (· ∉ T)).card := by
          intro v _
          have hunion : (H.neighborFinset v).filter (· ∈ T)
                ∪ (H.neighborFinset v).filter (· ∉ T)
              = H.neighborFinset v := by
            ext w
            simp only [Finset.mem_union, Finset.mem_filter]
            tauto
          have hdisj : Disjoint ((H.neighborFinset v).filter (· ∈ T))
              ((H.neighborFinset v).filter (· ∉ T)) := by
            rw [Finset.disjoint_left]
            intro w hw1 hw2
            rw [Finset.mem_filter] at hw1 hw2
            exact hw2.2 hw1.2
          rw [← Finset.card_union_of_disjoint hdisj, hunion]
        have hcross : ∑ v ∈ T, ((H.neighborFinset v).filter (· ∉ T)).card
            = ∑ w ∈ Finset.univ \ T,
              ((H.neighborFinset w).filter (· ∈ T)).card := by
          have hkey : ∀ v ∈ T, ((H.neighborFinset v).filter (· ∉ T)).card
              = ∑ w ∈ Finset.univ \ T,
                (if H.Adj v w then 1 else 0) := by
            intro v _
            have e1 : (H.neighborFinset v).filter (· ∉ T)
                = (Finset.univ \ T).filter (fun w => H.Adj v w) := by
              ext w
              simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
                Finset.mem_sdiff, Finset.mem_univ]
              tauto
            rw [e1, Finset.card_eq_sum_ones, Finset.sum_filter]
          have hkey2 : ∀ w ∈ Finset.univ \ T,
              ((H.neighborFinset w).filter (· ∈ T)).card
                = (∑ v ∈ T, (if H.Adj v w then 1 else 0)) := by
            intro w _
            have e2 : (H.neighborFinset w).filter (· ∈ T)
                = T.filter (fun v => H.Adj v w) := by
              ext v
              simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
              tauto
            rw [e2, Finset.card_eq_sum_ones, Finset.sum_filter]
          calc ∑ v ∈ T, ((H.neighborFinset v).filter (· ∉ T)).card
              = ∑ v ∈ T, ∑ w ∈ Finset.univ \ T,
                  (if H.Adj v w then 1 else 0) :=
                Finset.sum_congr rfl (fun v hv => hkey v hv)
            _ = ∑ w ∈ Finset.univ \ T, ∑ v ∈ T,
                  (if H.Adj v w then 1 else 0) := Finset.sum_comm
            _ = ∑ w ∈ Finset.univ \ T,
                  ((H.neighborFinset w).filter (· ∈ T)).card :=
                Finset.sum_congr rfl (fun w hw => (hkey2 w hw).symm)
        have hcross_le : ∀ w ∈ Finset.univ \ T,
            min (d w) r
              ≤ ((H.neighborFinset w).filter (· ∈ T)).card := by
          intro w hw
          rw [Finset.mem_sdiff] at hw
          have hwT : w ∉ T := hw.2
          have hfin_eq : (H.neighborFinset w).filter (· ∈ T)
              = (H.neighborSet w ∩ ↑T).toFinset := by
            ext v
            simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
              Set.mem_toFinset, Set.mem_inter_iff,
              SimpleGraph.mem_neighborSet, Finset.mem_coe]
          have hn_eq :=
            Set.ncard_eq_toFinset_card' (H.neighborSet w ∩ ↑T)
          rw [hfin_eq, ← hn_eq]
          exact hC2 w hwT
        have hsum_inside : ∑ v ∈ T,
            ((H.neighborFinset v).filter (· ∈ T)).card
              = r * (r - 1) := by
          have h1 : ∑ v ∈ T, ((H.neighborFinset v).filter (· ∈ T)).card
              = ∑ v ∈ T, (r - 1) :=
            Finset.sum_congr rfl (fun v hv => hinside v hv)
          rw [h1, Finset.sum_const, nsmul_eq_mul, Nat.cast_id, ← hr]
        have hsum_split : ∑ v ∈ T, (H.neighborFinset v).card
            = r * (r - 1)
              + ∑ w ∈ Finset.univ \ T,
                ((H.neighborFinset w).filter (· ∈ T)).card := by
          have e1 : ∑ v ∈ T, (H.neighborFinset v).card
              = ∑ v ∈ T, (((H.neighborFinset v).filter (· ∈ T)).card
                + ((H.neighborFinset v).filter (· ∉ T)).card) :=
            Finset.sum_congr rfl (fun v hv => hsplit v hv)
          rw [e1, Finset.sum_add_distrib, hsum_inside, hcross]
        have hmin_le : ∑ w ∈ Finset.univ \ T, min (d w) r
            ≤ ∑ w ∈ Finset.univ \ T,
              ((H.neighborFinset w).filter (· ∈ T)).card :=
          Finset.sum_le_sum (fun w hw => hcross_le w hw)
        omega
      -- Convert the ncard saturation back to `degree`.
      let : DecidableRel H.Adj := Classical.decRel _
      have hsat : ∀ v, H.degree v = d v := by
        intro v
        have h := SimpleGraph.ncard_neighborSet (G := H) (v := v)
        have hn := hsat_nc v
        omega
      exact ⟨H, inferInstance, hsat⟩

end MathlibExt.Combinatorics.SimpleGraph.ErdosGallaiWanted
end
