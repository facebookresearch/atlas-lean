/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
public import Mathlib.Topology.EMetricSpace.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

namespace MathlibExt.Analysis.Convex.KKM

/-!
# Knaster-Kuratowski-Mazurkiewicz lemma

Proved via Sperner's lemma on iterated barycentric subdivisions plus a
mesh-shrinking limit argument: fully labeled simplices at every level, a
convergent subsequence in the compact simplex (mesh `(n/(n+1))^k → 0`), and
closedness of the cover. Vertices at level `k+1` are finsets of level-`k`
vertices; validity means a nonempty chain with supports in the coordinate
set; `BdPt` is barycentric realization in `Convexity.StdSimplex`.

Primary source: B. Knaster, C. Kuratowski, S. Mazurkiewicz,
"Ein Beweis des Fixpunktsatzes für n-dimensionale Simplexe",
Fundamenta Mathematicae 14 (1929), 132–137, DOI 10.4064/fm-14-1-132-137.
-/

variable {n : ℕ}

/-- Vertices at subdivision level `k`: level 0 is `Fin (n+1)`; higher levels
are (valid) simplices of the previous level, as bare finsets. -/
private def BdV : ℕ → Type
  | 0 => Fin (n + 1)
  | k + 1 => Finset (BdV k)

/-- View a higher-level vertex as a finset (explicit projection so that
unification sees the `Finset` type; bare ascriptions do not propagate). -/
private def BdFin {k : ℕ} (a : BdV (n := n) (k + 1)) : Finset (BdV (n := n) k) := a

/-- View a level-0 vertex as a simplex index. -/
private def BdFin0 (i : BdV (n := n) 0) : Fin (n + 1) := i

private instance bdVDecEq : ∀ k, DecidableEq (BdV (n := n) k)
  | 0 => by change DecidableEq (Fin (n + 1)); exact inferInstance
  | k + 1 => by
      change DecidableEq (Finset (BdV (n := n) k))
      haveI : DecidableEq (BdV (n := n) k) := bdVDecEq k
      exact inferInstance

private instance bdVFin : ∀ k, Fintype (BdV (n := n) k)
  | 0 => by change Fintype (Fin (n + 1)); exact inferInstance
  | k + 1 => by
      change Fintype (Finset (BdV (n := n) k))
      haveI : Fintype (BdV (n := n) k) := bdVFin k
      haveI : DecidableEq (BdV (n := n) k) := bdVDecEq k
      exact inferInstance

/-- Validity of a simplex over coordinate set `S`: level 0 means a nonempty
sub-vertex-set of `S`; higher levels mean a nonempty chain of valid
simplices. -/
private def BdValid (S : Finset (Fin (n + 1))) : ∀ k, Finset (BdV (n := n) k) → Prop
  | 0, σ => σ ⊆ S ∧ σ.Nonempty
  | k + 1, σ =>
      (∀ a ∈ (σ : Set (BdV (n := n) (k + 1))), ∀ b ∈ (σ : Set (BdV (n := n) (k + 1))),
        BdFin a ⊆ BdFin b ∨ BdFin b ⊆ BdFin a) ∧
      (∀ v ∈ σ, BdValid S k v) ∧ σ.Nonempty

/-- Geometric realization: vertices go to simplex vertices; higher vertices
to barycenters. -/
private noncomputable def BdPt : ∀ k, BdV (n := n) k → (Fin (n + 1) → ℝ)
  | 0, i => fun j => if j = BdFin0 i then 1 else 0
  | k + 1, σ => fun j => (∑ v ∈ BdFin σ, BdPt k v j) / ((BdFin σ).card : ℝ)

/-- Coordinate support of a vertex. -/
private def BdSupp : ∀ k, BdV (n := n) k → Finset (Fin (n + 1))
  | 0, i => {BdFin0 i}
  | k + 1, σ => (BdFin σ).biUnion (BdSupp k)

/-- Valid simplices are nonempty at every level. -/
private lemma nonempty_of_valid {S : Finset (Fin (n + 1))} :
    ∀ {k} {σ : Finset (BdV (n := n) k)}, BdValid S k σ → σ.Nonempty
  | 0, _, h => h.2
  | _ + 1, _, h => h.2.2

/-- Valid simplices have cardinality at most `|S|` and at least 1. -/
private lemma card_of_valid {S : Finset (Fin (n + 1))} :
    ∀ {k} {σ : Finset (BdV (n := n) k)},
      BdValid S k σ → 1 ≤ σ.card ∧ σ.card ≤ S.card := by
  intro k
  induction k with
  | zero =>
    intro σ h
    refine ⟨Finset.card_pos.mpr h.2, Finset.card_le_card h.1⟩
  | succ k ih =>
    intro σ h
    obtain ⟨hchain, hmem, hne⟩ := h
    have hpos : 1 ≤ σ.card := Finset.card_pos.mpr hne
    refine ⟨hpos, ?_⟩
    -- element cards are distinct values in {1, ..., |S|}
    have hmem' : ∀ v ∈ σ, 1 ≤ (BdFin v).card ∧ (BdFin v).card ≤ S.card :=
      fun v hv => ih (hmem v hv)
    have hinj : Set.InjOn (fun v : BdV (n := n) (k + 1) => (BdFin v).card) ↑σ := by
      intro a ha b hb hab
      by_contra hne2
      have hcomp := hchain a ha b hb
      have hlt : (BdFin a).card ≠ (BdFin b).card := by
        cases hcomp with
        | inl hsub =>
          have hss : BdFin a ⊂ BdFin b :=
            ⟨hsub, fun hle => hne2 (Finset.Subset.antisymm hsub hle)⟩
          have := Finset.card_lt_card hss
          omega
        | inr hsub =>
          have hss : BdFin b ⊂ BdFin a :=
            ⟨hsub, fun hle => hne2 (Finset.Subset.antisymm hsub hle).symm⟩
          have := Finset.card_lt_card hss
          omega
      exact hlt hab
    have himg : σ.image (fun v : BdV (n := n) (k + 1) => (BdFin v).card) ⊆
        Finset.Icc 1 S.card := by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
      have ha' := hmem' a ha
      exact Finset.mem_Icc.mpr ha'
    calc σ.card = (σ.image (fun v : BdV (n := n) (k + 1) =>
            (BdFin v).card)).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Icc 1 S.card).card := Finset.card_le_card himg
      _ = S.card := by rw [Nat.card_Icc]; omega

/-- Membership in coordinate support at level 0. -/
private lemma mem_BdSupp_zero {i : BdV (n := n) 0} {j : Fin (n + 1)} :
    j ∈ BdSupp 0 i ↔ j = BdFin0 i := Finset.mem_singleton

/-- Membership in coordinate support at higher levels. -/
private lemma mem_BdSupp_succ {k : ℕ} {σ : BdV (n := n) (k + 1)}
    {j : Fin (n + 1)} :
    j ∈ BdSupp (k + 1) σ ↔ ∃ v ∈ BdFin σ, j ∈ BdSupp k v :=
  Finset.mem_biUnion

/-- Singletons of members of valid sets are valid. -/
private lemma valid_singleton_of_mem {S : Finset (Fin (n + 1))} :
    ∀ {k} {σ : Finset (BdV (n := n) k)} {w : BdV (n := n) k},
      BdValid S k σ → w ∈ σ → BdValid S k {w} := by
  intro k
  induction k with
  | zero =>
    intro σ w h hw
    refine ⟨?_, Finset.singleton_nonempty w⟩
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact h.1 hw
  | succ k ih =>
    intro σ w h hw
    obtain ⟨hchain, hmem, hne⟩ := h
    refine ⟨?_, ?_, Finset.singleton_nonempty w⟩
    · intro a ha b hb
      rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
      subst ha
      subst hb
      exact Or.inl (Finset.Subset.refl _)
    · intro v hv
      rw [Finset.mem_singleton] at hv
      subst v
      exact hmem w hw

/-- Coordinate support of a valid vertex lies in the coordinate set. -/
private lemma BdSupp_subset {S : Finset (Fin (n + 1))} :
    ∀ {k} {v : BdV (n := n) k}, BdValid S k {v} → BdSupp k v ⊆ S := by
  intro k
  induction k with
  | zero =>
    intro v hv j hj
    rw [mem_BdSupp_zero] at hj
    obtain rfl := hj
    exact hv.1 (Finset.mem_singleton_self _)
  | succ k ih =>
    intro v hv j hj
    rw [mem_BdSupp_succ] at hj
    obtain ⟨w, hw, hjw⟩ := hj
    obtain ⟨hchain, hmem, hne⟩ := hv
    have hvset : BdValid S k (BdFin v) := hmem v (Finset.mem_singleton_self v)
    exact ih (valid_singleton_of_mem hvset hw) hjw

/-- Barycentric coordinates vanish outside the support. -/
private lemma BdPt_eq_zero_of_not_mem_supp {k : ℕ} {v : BdV (n := n) k}
    {j : Fin (n + 1)} (hj : j ∉ BdSupp k v) : BdPt k v j = 0 := by
  induction k with
  | zero =>
    change (if j = BdFin0 v then (1 : ℝ) else 0) = 0
    apply ite_eq_right
    intro hcon
    subst hcon
    exact hj (Finset.mem_singleton_self _)
  | succ k ih =>
    change (∑ w ∈ BdFin v, BdPt k w j) / ((BdFin v).card : ℝ) = 0
    have h0 : (∑ w ∈ BdFin v, BdPt k w j) = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      apply ih
      intro hcon
      exact hj (mem_BdSupp_succ.mpr ⟨w, hw, hcon⟩)
    rw [h0, zero_div]

/-- Barycentric coordinates are nonnegative on valid vertices. -/
private lemma BdPt_nonneg {S : Finset (Fin (n + 1))} :
    ∀ {k} {v : BdV (n := n) k},
      BdValid S k {v} → ∀ j, 0 ≤ BdPt k v j := by
  intro k
  induction k with
  | zero =>
    intro v hv j
    change 0 ≤ (if j = BdFin0 v then (1 : ℝ) else 0)
    split_ifs <;> positivity
  | succ k ih =>
    intro v hv j
    obtain ⟨hchain, hmem, hne⟩ := hv
    have hvset : BdValid S k (BdFin v) := hmem v (Finset.mem_singleton_self v)
    have hne' : (BdFin v).Nonempty := nonempty_of_valid hvset
    have hcard_pos : (0 : ℝ) < (BdFin v).card := by
      rw [Nat.cast_pos]
      exact Finset.card_pos.mpr hne'
    change 0 ≤ (∑ w ∈ BdFin v, BdPt k w j) / ((BdFin v).card : ℝ)
    apply div_nonneg _ (le_of_lt hcard_pos)
    apply Finset.sum_nonneg
    intro w hw
    exact ih (valid_singleton_of_mem hvset hw) j

/-- Barycentric coordinates sum to one on valid vertices. -/
private lemma BdPt_sum {S : Finset (Fin (n + 1))} :
    ∀ {k} {v : BdV (n := n) k},
      BdValid S k {v} → ∑ j, BdPt k v j = 1 := by
  intro k
  induction k with
  | zero =>
    intro v hv
    change (∑ j, (if j = BdFin0 v then (1 : ℝ) else 0)) = 1
    rw [Finset.sum_ite_eq']
    simp
  | succ k ih =>
    intro v hv
    obtain ⟨hchain, hmem, hne⟩ := hv
    have hvset : BdValid S k (BdFin v) := hmem v (Finset.mem_singleton_self v)
    have hne' : (BdFin v).Nonempty := nonempty_of_valid hvset
    have hcard_pos : (0 : ℝ) < (BdFin v).card := by
      rw [Nat.cast_pos]
      exact Finset.card_pos.mpr hne'
    have hsum : ∀ w ∈ BdFin v, ∑ j, BdPt k w j = 1 :=
      fun w hw => ih (valid_singleton_of_mem hvset hw)
    change (∑ j, (∑ w ∈ BdFin v, BdPt k w j) / ((BdFin v).card : ℝ)) = 1
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    have hsum' : (∑ j, ∑ w ∈ BdFin v, BdPt k w j) = ((BdFin v).card : ℝ) := by
      rw [Finset.sum_comm]
      rw [Finset.sum_congr rfl (fun w hw => hsum w hw)]
      simp
    rw [hsum']
    exact mul_inv_cancel₀ (ne_of_gt hcard_pos)

/-- Valid vertices as points of the new standard simplex. -/
private noncomputable def BdSimp {S : Finset (Fin (n + 1))}
    {k : ℕ} {v : BdV (n := n) k} (hv : BdValid S k {v}) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) where
  weights := Finsupp.equivFunOnFinite.symm (BdPt k v)
  nonneg m := by simpa using BdPt_nonneg hv m
  total := by simpa [Finsupp.sum_fintype] using BdPt_sum hv

/-- Coordinate characteristic for the new-simplex packaging. -/
private lemma BdSimp_weights {S : Finset (Fin (n + 1))}
    {k : ℕ} {v : BdV (n := n) k} (hv : BdValid S k {v}) (j : Fin (n + 1)) :
    (BdSimp hv).weights j = BdPt k v j := rfl

/-- Every valid vertex has a support coordinate whose closed cover set
contains the vertex point. -/
private lemma BdLabel_exists {k : ℕ}
    (F : Fin (n + 1) → Set (Convexity.StdSimplex ℝ (Fin (n + 1))))
    (hF_cover : ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∃ i : Fin (n + 1), 0 < x.weights i ∧ x ∈ F i)
    {S : Finset (Fin (n + 1))}
    (v : BdV (n := n) k) (hv : BdValid S k {v}) :
    ∃ i, i ∈ BdSupp k v ∧ BdSimp hv ∈ F i := by
  obtain ⟨i, hi_pos, hiF⟩ := hF_cover (BdSimp hv)
  refine ⟨i, ?_, hiF⟩
  by_contra hcon
  have h0 : BdPt k v i = 0 := BdPt_eq_zero_of_not_mem_supp hcon
  have hcoe : (BdSimp hv).weights i = BdPt k v i := BdSimp_weights hv i
  rw [hcoe, h0] at hi_pos
  exact (lt_irrefl _ hi_pos).elim

/-- Sperner labeling derived from the closed cover (0 on invalid vertices). -/
private noncomputable def BdLabel {k : ℕ}
    (F : Fin (n + 1) → Set (Convexity.StdSimplex ℝ (Fin (n + 1))))
    (hF_cover : ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∃ i : Fin (n + 1), 0 < x.weights i ∧ x ∈ F i)
    (S : Finset (Fin (n + 1))) (v : BdV (n := n) k) : Fin (n + 1) := by
  classical
  exact dite (BdValid S k {v})
    (fun hv => Classical.choose (BdLabel_exists F hF_cover v hv)) (fun _ => 0)

/-- The Sperner label lies in the support. -/
private lemma BdLabel_mem_supp {k : ℕ}
    {F : Fin (n + 1) → Set (Convexity.StdSimplex ℝ (Fin (n + 1)))}
    {hF_cover : ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∃ i : Fin (n + 1), 0 < x.weights i ∧ x ∈ F i}
    {S : Finset (Fin (n + 1))} {v : BdV (n := n) k}
    (hv : BdValid S k {v}) : BdLabel F hF_cover S v ∈ BdSupp k v := by
  simp only [BdLabel, dite_eq_left hv]
  exact (Classical.choose_spec (BdLabel_exists F hF_cover v hv)).1

/-- The Sperner label's closed set contains the vertex point. -/
private lemma BdLabel_mem_cover {k : ℕ}
    {F : Fin (n + 1) → Set (Convexity.StdSimplex ℝ (Fin (n + 1)))}
    {hF_cover : ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∃ i : Fin (n + 1), 0 < x.weights i ∧ x ∈ F i}
    {S : Finset (Fin (n + 1))} {v : BdV (n := n) k}
    (hv : BdValid S k {v}) :
    BdSimp hv ∈ F (BdLabel F hF_cover S v) := by
  simp only [BdLabel, dite_eq_left hv]
  exact (Classical.choose_spec (BdLabel_exists F hF_cover v hv)).2

/-- Single-simplex parity, onto case: exactly one omitted-vertex facet has
label-set `t.erase c`. -/
private lemma single_parity_surj {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (c : β) (hc : c ∈ t) (l : α → β)
    (hmaps : ∀ v ∈ s, l v ∈ t) (hm : s.card = t.card)
    (him : s.image l = t) :
    (s.filter (fun v => (s.erase v).image l = t.erase c)).card % 2 = 1 := by
  have hFib1 : ∀ y ∈ t, (s.filter (fun v => l v = y)).card ≥ 1 := by
    intro y hy
    have hy' : y ∈ s.image l := by rw [him]; exact hy
    obtain ⟨v, hvs, hvy⟩ := Finset.mem_image.mp hy'
    exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hvs, hvy⟩⟩
  have hpart : ∑ y ∈ t, (s.filter (fun v => l v = y)).card = t.card := by
    have hunion : s = t.biUnion (fun y => s.filter (fun v => l v = y)) := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hvs
        exact ⟨l v, hmaps v hvs, hvs, rfl⟩
      · intro h
        obtain ⟨y, hy, hvs, hvy⟩ := h
        exact hvs
    have hdisj : Set.PairwiseDisjoint (↑t)
        (fun y => s.filter (fun v => l v = y)) := by
      intro y1 _ y2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      rw [Finset.mem_filter] at hv1 hv2
      exact hne (hv1.2.symm.trans hv2.2)
    calc ∑ y ∈ t, (s.filter (fun v => l v = y)).card
        = (t.biUnion (fun y => s.filter (fun v => l v = y))).card :=
          (Finset.card_biUnion hdisj).symm
      _ = s.card := by rw [← hunion]
      _ = t.card := hm
  have hsingle : ∀ y ∈ t, (s.filter (fun v => l v = y)).card = 1 := by
    have hsum0 : ∑ y ∈ t, ((s.filter (fun v => l v = y)).card - 1) = 0 := by
      rw [Finset.sum_tsub_distrib _ (fun y hy => hFib1 y hy), hpart]
      simp
    have hall0 : ∀ z ∈ t, (s.filter (fun v => l v = z)).card - 1 = 0 := by
      intro z hz
      have hiff := Finset.sum_eq_zero_iff_of_nonneg
        (s := t) (f := fun y => (s.filter (fun v => l v = y)).card - 1)
        (fun _ _ => Nat.zero_le _)
      exact (hiff.mp hsum0) z hz
    intro y hy
    have h1 := hFib1 y hy
    have h0 := hall0 y hy
    omega
  obtain ⟨v0, hv0⟩ := Finset.card_eq_one.mp (hsingle c hc)
  have hG : s.filter (fun v => (s.erase v).image l = t.erase c) = {v0} := by
    ext v
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      obtain ⟨hvs, hgood⟩ := h
      have hcimg : c ∈ s.image l := by rw [him]; exact hc
      obtain ⟨w, hws, hw⟩ := Finset.mem_image.mp hcimg
      have hwfib : w ∈ s.filter (fun v => l v = c) :=
        Finset.mem_filter.mpr ⟨hws, hw⟩
      rw [hv0, Finset.mem_singleton] at hwfib
      by_contra hcon
      have hwne : w ≠ v := by
        rw [hwfib]
        exact fun h => hcon h.symm
      have hwerase : w ∈ s.erase v := Finset.mem_erase.mpr ⟨hwne, hws⟩
      have hcmem : c ∈ (s.erase v).image l :=
        Finset.mem_image.mpr ⟨w, hwerase, hw⟩
      rw [hgood] at hcmem
      exact Finset.notMem_erase c t hcmem
    · intro h
      subst v
      have hv0fib : v0 ∈ s.filter (fun v => l v = c) := by
        rw [hv0]
        exact Finset.mem_singleton_self v0
      rw [Finset.mem_filter] at hv0fib
      refine ⟨hv0fib.1, ?_⟩
      have hsub : (s.erase v0).image l ⊆ t.erase c := by
        intro y hy
        obtain ⟨w, hwerase, hwl⟩ := Finset.mem_image.mp hy
        rw [Finset.mem_erase] at hwerase
        rw [Finset.mem_erase]
        constructor
        · intro hcon
          have hlc : l w = c := hwl.trans hcon
          have hwfib : w ∈ s.filter (fun v => l v = c) :=
            Finset.mem_filter.mpr ⟨hwerase.2, hlc⟩
          rw [hv0, Finset.mem_singleton] at hwfib
          exact hwerase.1 hwfib
        · rw [← hwl]
          exact hmaps w hwerase.2
      have hcard : ((s.erase v0).image l).card = (t.erase c).card := by
        have hinj : Set.InjOn l ↑(s.erase v0) := by
          intro w1 hw1 w2 hw2 heq
          rw [Finset.mem_coe, Finset.mem_erase] at hw1 hw2
          have h1 : w1 ∈ s.filter (fun v => l v = l w1) :=
            Finset.mem_filter.mpr ⟨hw1.2, rfl⟩
          have h2 : w2 ∈ s.filter (fun v => l v = l w1) :=
            Finset.mem_filter.mpr ⟨hw2.2, heq.symm⟩
          have hsing := hsingle (l w1) (hmaps w1 hw1.2)
          obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hsing
          rw [hu, Finset.mem_singleton] at h1 h2
          exact h1.trans h2.symm
        rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hv0fib.1,
          Finset.card_erase_of_mem hc, hm]
      exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  rw [hG, Finset.card_singleton]

/-- Single-simplex parity, small-image case: no good facets. -/
private lemma single_parity_small {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (c : β) (hc : c ∈ t) (l : α → β)
    (hlt : (s.image l).card + 1 < t.card) :
    (s.filter (fun v => (s.erase v).image l = t.erase c)).card % 2 = 0 := by
  have hGempty : s.filter (fun v => (s.erase v).image l = t.erase c) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvs, hgood⟩ := hv
    have hsub : (s.erase v).image l ⊆ s.image l := by
      intro y hy
      obtain ⟨w, hwerase, hwl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨w, Finset.erase_subset v s hwerase, hwl⟩
    rw [hgood] at hsub
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hc] at hle
    have htpos : 1 ≤ t.card := Finset.card_pos.mpr ⟨c, hc⟩
    omega
  rw [hGempty, Finset.card_empty]

/-- Single-simplex parity, wrong-missing-label case: no good facets. -/
private lemma single_parity_wrong {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (c : β) (l : α → β)
    (d : β) (hd : d ∈ t) (hdc : d ≠ c) (hTd : s.image l = t.erase d) :
    (s.filter (fun v => (s.erase v).image l = t.erase c)).card % 2 = 0 := by
  have hGempty : s.filter (fun v => (s.erase v).image l = t.erase c) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvs, hgood⟩ := hv
    have hsub : (s.erase v).image l ⊆ t.erase d := by
      rw [← hTd]
      intro y hy
      obtain ⟨w, hwerase, hwl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨w, Finset.erase_subset v s hwerase, hwl⟩
    rw [hgood] at hsub
    have hdmem : d ∈ t.erase c := Finset.mem_erase.mpr ⟨hdc, hd⟩
    have hcon := hsub hdmem
    exact Finset.notMem_erase d t hcon
  rw [hGempty, Finset.card_empty]

/-- Single-simplex parity, doubled-fiber case: exactly two good facets. -/
private lemma single_parity_doubled {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (c : β) (hc : c ∈ t) (l : α → β)
    (_hmaps : ∀ v ∈ s, l v ∈ t) (hm : s.card = t.card)
    (hTd : s.image l = t.erase c) :
    (s.filter (fun v => (s.erase v).image l = t.erase c)).card % 2 = 0 := by
  have hFib1 : ∀ y ∈ t.erase c, (s.filter (fun v => l v = y)).card ≥ 1 := by
    intro y hy
    have hy' : y ∈ s.image l := by rw [hTd]; exact hy
    obtain ⟨v, hvs, hvy⟩ := Finset.mem_image.mp hy'
    exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hvs, hvy⟩⟩
  have hpart : ∑ y ∈ t.erase c, (s.filter (fun v => l v = y)).card = s.card := by
    have hunion : s = (t.erase c).biUnion
        (fun y => s.filter (fun v => l v = y)) := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hvs
        have hmem : l v ∈ t.erase c := by
          have himg : l v ∈ s.image l :=
            Finset.mem_image.mpr ⟨v, hvs, rfl⟩
          rw [hTd] at himg
          exact himg
        exact ⟨l v, hmem, hvs, rfl⟩
      · intro h
        obtain ⟨y, hy, hvs, hvy⟩ := h
        exact hvs
    have hdisj : Set.PairwiseDisjoint (↑(t.erase c))
        (fun y => s.filter (fun v => l v = y)) := by
      intro y1 _ y2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      rw [Finset.mem_filter] at hv1 hv2
      exact hne (hv1.2.symm.trans hv2.2)
    calc ∑ y ∈ t.erase c, (s.filter (fun v => l v = y)).card
        = ((t.erase c).biUnion (fun y => s.filter (fun v => l v = y))).card :=
          (Finset.card_biUnion hdisj).symm
      _ = s.card := by rw [← hunion]
  have hspos : 1 ≤ s.card := by
    rw [hm]
    exact Finset.card_pos.mpr ⟨c, hc⟩
  have hcardT : (t.erase c).card = s.card - 1 := by
    rw [Finset.card_erase_of_mem hc, ← hm]
  have hsum1 : ∑ y ∈ t.erase c, ((s.filter (fun v => l v = y)).card - 1) = 1 := by
    rw [Finset.sum_tsub_distrib _ (fun y hy => hFib1 y hy), hpart]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id]
    rw [hcardT]
    omega
  obtain ⟨tstar, htstar, hstar1, hstar0⟩ :
      ∃ tstar ∈ t.erase c, (s.filter (fun v => l v = tstar)).card = 2 ∧
        ∀ y ∈ t.erase c, y ≠ tstar →
          (s.filter (fun v => l v = y)).card = 1 := by
    have hex : ∃ tstar ∈ t.erase c,
        (s.filter (fun v => l v = tstar)).card - 1 ≠ 0 := by
      by_contra hcon
      have hall : ∀ tstar ∈ t.erase c,
          (s.filter (fun v => l v = tstar)).card - 1 = 0 := by
        intro tstar htstar
        by_contra hne2
        exact hcon ⟨tstar, htstar, hne2⟩
      have h0 := Finset.sum_eq_zero hall
      omega
    obtain ⟨tstar, htstar, hgne⟩ := hex
    have hub : ∀ y ∈ t.erase c,
        (s.filter (fun v => l v = y)).card - 1 ≠ 0 → y = tstar := by
      intro y hy hgy
      by_contra hne
      have hle : (s.filter (fun v => l v = tstar)).card - 1 +
          ((s.filter (fun v => l v = y)).card - 1) ≤
          ∑ z ∈ t.erase c, ((s.filter (fun v => l v = z)).card - 1) := by
        have hsub : ({tstar, y} : Finset β) ⊆ t.erase c := by
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact htstar
          · exact hy
        have hle2 := Finset.sum_le_sum_of_subset_of_nonneg
          (s := ({tstar, y} : Finset β)) (t := t.erase c)
          (f := fun z => (s.filter (fun v => l v = z)).card - 1)
          hsub (fun _ _ _ => Nat.zero_le _)
        rw [Finset.sum_pair (fun h => hne h.symm)] at hle2
        exact hle2
      have g1 : 1 ≤ (s.filter (fun v => l v = tstar)).card - 1 :=
        Nat.pos_of_ne_zero hgne
      have g2 : 1 ≤ (s.filter (fun v => l v = y)).card - 1 :=
        Nat.pos_of_ne_zero hgy
      omega
    have h1 : (s.filter (fun v => l v = tstar)).card - 1 = 1 := by
      have hsingle0 := Finset.sum_eq_single tstar
        (s := t.erase c) (f := fun y => (s.filter (fun v => l v = y)).card - 1)
        (fun y hy hne => by
          by_contra hgy
          exact hne (hub y hy hgy))
        (fun h => absurd htstar h)
      omega
    refine ⟨tstar, htstar, ?_, ?_⟩
    · have hfi := hFib1 tstar htstar
      omega
    · intro y hy hne
      by_contra hcon
      have hgy : (s.filter (fun v => l v = y)).card - 1 ≠ 0 := by
        have hfi := hFib1 y hy
        omega
      exact hne (hub y hy hgy)
  have hGchar : ∀ v ∈ s, ((s.erase v).image l = t.erase c ↔
      2 ≤ (s.filter (fun w => l w = l v)).card) := by
    intro v hvs
    constructor
    · intro hgood
      have hmem : l v ∈ t.erase c := by
        have himg : l v ∈ s.image l :=
          Finset.mem_image.mpr ⟨v, hvs, rfl⟩
        rw [hTd] at himg
        exact himg
      rw [← hgood] at hmem
      obtain ⟨w, hwerase, hwl⟩ := Finset.mem_image.mp hmem
      rw [Finset.mem_erase] at hwerase
      have hsub : ({v, w} : Finset α) ⊆ s.filter (fun u => l u = l v) := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_filter.mpr ⟨hvs, rfl⟩
        · exact Finset.mem_filter.mpr ⟨hwerase.2, hwl⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_pair hwerase.1.symm] at hle
      exact hle
    · intro h2
      have hsub1 : (s.erase v).image l ⊆ t.erase c := by
        intro y hy
        obtain ⟨w, hwerase, hwl⟩ := Finset.mem_image.mp hy
        rw [Finset.mem_erase]
        constructor
        · intro hcon
          have himg : l w ∈ s.image l := Finset.mem_image.mpr
            ⟨w, Finset.erase_subset v s hwerase, rfl⟩
          rw [hTd, Finset.mem_erase] at himg
          exact himg.1 (hwl.trans hcon)
        · have himg : l w ∈ s.image l := Finset.mem_image.mpr
            ⟨w, Finset.erase_subset v s hwerase, rfl⟩
          rw [hTd, Finset.mem_erase] at himg
          rw [← hwl]
          exact himg.2
      have hsub2 : t.erase c ⊆ (s.erase v).image l := by
        intro y hy
        rw [Finset.mem_erase] at hy
        obtain ⟨hync, hyt⟩ := hy
        have hyimg : y ∈ s.image l := by
          rw [hTd]
          exact Finset.mem_erase.mpr ⟨hync, hyt⟩
        obtain ⟨u, hus, huy⟩ := Finset.mem_image.mp hyimg
        by_cases huv : u = v
        · subst u
          have hmemv : v ∈ s.filter (fun w => l w = l v) :=
            Finset.mem_filter.mpr ⟨hvs, rfl⟩
          have hss : ({v} : Finset α) ⊂ s.filter (fun w => l w = l v) := by
            refine ⟨?_, ?_⟩
            · intro x hx
              rw [Finset.mem_singleton] at hx
              obtain rfl := hx
              exact hmemv
            · intro hcon
              have hle := Finset.card_le_card hcon
              rw [Finset.card_singleton] at hle
              omega
          obtain ⟨w, hwfib, hwnsing⟩ := Finset.exists_of_ssubset hss
          rw [Finset.mem_filter] at hwfib
          rw [Finset.mem_singleton] at hwnsing
          have hwerase : w ∈ s.erase v :=
            Finset.mem_erase.mpr ⟨hwnsing, hwfib.1⟩
          have huy2 : l w = y := hwfib.2.trans huy
          exact Finset.mem_image.mpr ⟨w, hwerase, huy2⟩
        · have huerase : u ∈ s.erase v := Finset.mem_erase.mpr ⟨huv, hus⟩
          exact Finset.mem_image.mpr ⟨u, huerase, huy⟩
      exact Finset.Subset.antisymm hsub1 hsub2
  have hGeq : s.filter (fun v => (s.erase v).image l = t.erase c) =
      s.filter (fun v => l v = tstar) := by
    ext v
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro h
      obtain ⟨hvs, hgood⟩ := h
      have h2 := (hGchar v hvs).mp hgood
      have hmem : l v ∈ t.erase c := by
        have himg : l v ∈ s.image l :=
          Finset.mem_image.mpr ⟨v, hvs, rfl⟩
        rw [hTd] at himg
        exact himg
      have heq : l v = tstar := by
        by_contra hne
        have h1 := hstar0 (l v) hmem hne
        omega
      exact ⟨hvs, heq⟩
    · intro h
      obtain ⟨hvs, hlv⟩ := h
      refine ⟨hvs, ?_⟩
      have h2 : 2 ≤ (s.filter (fun w => l w = l v)).card := by
        rw [hlv]
        omega
      exact (hGchar v hvs).mpr h2
  rw [hGeq, hstar1]

/-- Single-simplex Sperner parity: the number of omitted-vertex facets with
label-set `t.erase c` is odd iff the labeling is onto `t`. -/
private lemma single_parity {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (c : β) (hc : c ∈ t) (l : α → β)
    (hmaps : ∀ v ∈ s, l v ∈ t) (hm : s.card = t.card) :
    (s.filter (fun v => (s.erase v).image l = t.erase c)).card % 2 =
      (if s.image l = t then 1 else 0) := by
  by_cases him : s.image l = t
  · rw [ite_eq_left him]
    exact single_parity_surj s t c hc l hmaps hm him
  · rw [ite_eq_right him]
    have himgsub : s.image l ⊆ t := by
      intro y hy
      obtain ⟨v, hvs, hvy⟩ := Finset.mem_image.mp hy
      rw [← hvy]
      exact hmaps v hvs
    have hcardlt : (s.image l).card < t.card :=
      Finset.card_lt_card ⟨himgsub, fun h => him (Finset.Subset.antisymm himgsub h)⟩
    by_cases hcard : (s.image l).card + 1 = t.card
    · obtain ⟨d, hd, hTd⟩ : ∃ d ∈ t, s.image l = t.erase d := by
        have hcompl : (t \ s.image l).card = 1 := by
          have hinter : s.image l ∩ t = s.image l := by
            ext y
            simp only [Finset.mem_inter]
            constructor
            · exact And.left
            · intro hy
              exact ⟨hy, himgsub hy⟩
          rw [Finset.card_sdiff, hinter]
          omega
        obtain ⟨d, hdeq⟩ := Finset.card_eq_one.mp hcompl
        have hdmem : d ∈ t := by
          have hmem : d ∈ t \ s.image l := by
            rw [hdeq]
            exact Finset.mem_singleton_self d
          exact (Finset.mem_sdiff.mp hmem).1
        refine ⟨d, hdmem, ?_⟩
        ext y
        constructor
        · intro hy
          rw [Finset.mem_erase]
          refine ⟨?_, himgsub hy⟩
          intro hcon
          subst y
          have hdT : d ∈ t \ s.image l := by
            rw [hdeq]
            exact Finset.mem_singleton_self d
          exact (Finset.mem_sdiff.mp hdT).2 hy
        · intro hy
          rw [Finset.mem_erase] at hy
          by_contra hcon
          have hmem : y ∈ t \ s.image l := Finset.mem_sdiff.mpr ⟨hy.2, hcon⟩
          rw [hdeq, Finset.mem_singleton] at hmem
          exact hy.1 hmem
      by_cases hdc : d = c
      · subst d
        exact single_parity_doubled s t c hc l hmaps hm hTd
      · exact single_parity_wrong s t c l d hd hdc hTd
    · have hlt : (s.image l).card + 1 < t.card := by omega
      exact single_parity_small s t c hc l hlt

/-- Union of coordinate supports over a set. -/
private def BdSuppSet (k : ℕ) (σ : Finset (BdV (n := n) k)) :
    Finset (Fin (n + 1)) :=
  σ.biUnion (BdSupp k)

private lemma mem_BdSuppSet {k : ℕ} {σ : Finset (BdV (n := n) k)}
    {j : Fin (n + 1)} :
    j ∈ BdSuppSet k σ ↔ ∃ v ∈ σ, j ∈ BdSupp k v := Finset.mem_biUnion

/-- Support is monotone in vertex inclusion (at levels ≥ 1). -/
private lemma BdSupp_mono_succ {k : ℕ} {a b : BdV (n := n) (k + 1)}
    (h : BdFin a ⊆ BdFin b) : BdSupp (k + 1) a ⊆ BdSupp (k + 1) b := by
  intro j hj
  rw [mem_BdSupp_succ] at hj ⊢
  obtain ⟨w, hw, hjw⟩ := hj
  exact ⟨w, h hw, hjw⟩

/-- A valid set with full cardinality has full support union. -/
private lemma supp_full_of_card_full {S : Finset (Fin (n + 1))} :
    ∀ {k} {c : Finset (BdV (n := n) k)},
      BdValid S k c → c.card = S.card → BdSuppSet k c = S := by
  intro k
  induction k with
  | zero =>
    intro c hc hcard
    have hsub : c ⊆ S := hc.1
    have heq : c = S := Finset.eq_of_subset_of_card_le hsub hcard.ge
    ext j
    rw [mem_BdSuppSet]
    constructor
    · intro h
      obtain ⟨v, hvc, hjv⟩ := h
      rw [mem_BdSupp_zero] at hjv
      subst hjv
      exact hsub hvc
    · intro hj
      have hjc : j ∈ c := by
        rw [heq]
        exact hj
      refine ⟨j, hjc, ?_⟩
      exact Finset.mem_singleton_self j
  | succ k ih =>
    intro c hc hcard
    obtain ⟨hchain, hmem, hne⟩ := hc
    have hinj : Set.InjOn (fun v : BdV (n := n) (k + 1) => (BdFin v).card)
        ↑c := by
      intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      by_contra hne2
      have hab' : (BdFin a).card = (BdFin b).card := hab
      have hcomp := hchain a ha b hb
      cases hcomp with
      | inl hsub2 =>
        have hss : BdFin a ⊂ BdFin b :=
          ⟨hsub2, fun hle => hne2 (Finset.Subset.antisymm hsub2 hle)⟩
        have hlt := Finset.card_lt_card hss
        omega
      | inr hsub2 =>
        have hss : BdFin b ⊂ BdFin a :=
          ⟨hsub2, fun hle => hne2 (Finset.Subset.antisymm hsub2 hle).symm⟩
        have hlt := Finset.card_lt_card hss
        omega
    have hcards : Finset.image (fun v : BdV (n := n) (k + 1) => (BdFin v).card)
        c = Finset.Icc 1 S.card := by
      have hsub : Finset.image (fun v : BdV (n := n) (k + 1) => (BdFin v).card)
          c ⊆ Finset.Icc 1 S.card := by
        intro m hmimg
        obtain ⟨v, hvc, rfl⟩ := Finset.mem_image.mp hmimg
        have hv : BdValid S k (BdFin v) := hmem v hvc
        have hbd := card_of_valid hv
        exact Finset.mem_Icc.mpr hbd
      have hcard_img : (Finset.image
          (fun v : BdV (n := n) (k + 1) => (BdFin v).card) c).card =
          (Finset.Icc 1 S.card).card := by
        rw [Finset.card_image_of_injOn hinj, hcard, Nat.card_Icc]
        omega
      exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard_img.symm)
    have hcpos : 1 ≤ S.card := by
      rw [← hcard]
      exact Finset.card_pos.mpr hne
    have hmaxmem : S.card ∈ Finset.image
        (fun v : BdV (n := n) (k + 1) => (BdFin v).card) c := by
      rw [hcards]
      exact Finset.mem_Icc.mpr ⟨hcpos, le_rfl⟩
    obtain ⟨wstar, hwstar, hstarcard⟩ := Finset.mem_image.mp hmaxmem
    have hstarcard' : (BdFin wstar).card = S.card := hstarcard
    have hunion : BdSuppSet (k + 1) c = BdSupp (k + 1) wstar := by
      apply Finset.Subset.antisymm
      · intro j hj
        rw [mem_BdSuppSet] at hj
        obtain ⟨v, hvc, hjv⟩ := hj
        have hcomp := hchain v (Finset.mem_coe.mpr hvc) wstar
          (Finset.mem_coe.mpr hwstar)
        have hsub : BdFin v ⊆ BdFin wstar := by
          cases hcomp with
          | inl h => exact h
          | inr h =>
            have hv : BdValid S k (BdFin v) := hmem v hvc
            have hbd := card_of_valid hv
            have hle := Finset.card_le_card h
            have heq : BdFin wstar = BdFin v :=
              Finset.eq_of_subset_of_card_le h (by omega)
            rw [← heq]
        exact BdSupp_mono_succ hsub hjv
      · intro j hj
        rw [mem_BdSuppSet]
        exact ⟨wstar, hwstar, hj⟩
    have hsupp : BdSupp (k + 1) wstar = S := by
      have hvalid : BdValid S k (BdFin wstar) := hmem wstar hwstar
      have hIH := ih hvalid hstarcard'
      change (BdFin wstar).biUnion (BdSupp k) = S
      exact hIH
    rw [hunion, hsupp]

/-- Members of valid sets have cards in range. -/
private lemma card_mem_valid {S : Finset (Fin (n + 1))} {k : ℕ}
    {τ : Finset (BdV (n := n) (k + 1))} (hτ : BdValid S (k + 1) τ)
    {v : BdV (n := n) (k + 1)} (hv : v ∈ τ) :
    1 ≤ (BdFin v).card ∧ (BdFin v).card ≤ S.card := by
  obtain ⟨hchain, hmem, hne⟩ := hτ
  have hvv : BdValid S k (BdFin v) := hmem v hv
  exact card_of_valid hvv

/-- Distinct chain elements have distinct cards. -/
private lemma cards_ne_of_ne {k : ℕ} {τ : Finset (BdV (n := n) (k + 1))}
    (hchain : ∀ a ∈ (τ : Set (BdV (n := n) (k + 1))),
      ∀ b ∈ (τ : Set (BdV (n := n) (k + 1))),
      BdFin a ⊆ BdFin b ∨ BdFin b ⊆ BdFin a)
    {a b : BdV (n := n) (k + 1)} (ha : a ∈ τ) (hb : b ∈ τ) (hne : a ≠ b) :
    (BdFin a).card ≠ (BdFin b).card := by
  have hcomp := hchain a (Finset.mem_coe.mpr ha) b (Finset.mem_coe.mpr hb)
  cases hcomp with
  | inl h =>
    have hss : BdFin a ⊂ BdFin b :=
      ⟨h, fun hle => hne (Finset.Subset.antisymm h hle)⟩
    have hlt := Finset.card_lt_card hss
    omega
  | inr h =>
    have hss : BdFin b ⊂ BdFin a :=
      ⟨h, fun hle => hne (Finset.Subset.antisymm h hle).symm⟩
    have hlt := Finset.card_lt_card hss
    omega

/-- A facet misses exactly one card value. -/
private lemma missing_card_exists {S : Finset (Fin (n + 1))} {k : ℕ}
    {τ : Finset (BdV (n := n) (k + 1))} (hτ : BdValid S (k + 1) τ)
    (hcard : τ.card = S.card - 1) :
    ∃ m, 1 ≤ m ∧ m ≤ S.card ∧ (∀ v ∈ τ, (BdFin v).card ≠ m) ∧
      ∀ m', 1 ≤ m' → m' ≤ S.card → m' ≠ m →
        ∃ v ∈ τ, (BdFin v).card = m' := by
  obtain ⟨hchain, hmem, hne⟩ := hτ
  have hS2 : 2 ≤ S.card := by
    have hpos := Finset.card_pos.mpr hne
    omega
  have hinj : Set.InjOn (fun v : BdV (n := n) (k + 1) => (BdFin v).card)
      ↑τ := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    have hab' : (BdFin a).card = (BdFin b).card := hab
    by_contra hne2
    exact cards_ne_of_ne hchain ha hb hne2 hab'
  have hsub : Finset.image (fun v : BdV (n := n) (k + 1) => (BdFin v).card)
      τ ⊆ Finset.Icc 1 S.card := by
    intro m hmimg
    obtain ⟨v, hvc, rfl⟩ := Finset.mem_image.mp hmimg
    have hvv : BdValid S k (BdFin v) := hmem v hvc
    exact Finset.mem_Icc.mpr (card_of_valid hvv)
  have hcard_img : (Finset.image
      (fun v : BdV (n := n) (k + 1) => (BdFin v).card) τ).card =
      S.card - 1 := by
    rw [Finset.card_image_of_injOn hinj, hcard]
  have hcompl : (Finset.Icc 1 S.card \ Finset.image
      (fun v : BdV (n := n) (k + 1) => (BdFin v).card) τ).card = 1 := by
    have hinter : Finset.image (fun v : BdV (n := n) (k + 1) => (BdFin v).card)
        τ ∩ Finset.Icc 1 S.card =
        Finset.image (fun v : BdV (n := n) (k + 1) => (BdFin v).card) τ := by
      ext y
      simp only [Finset.mem_inter]
      constructor
      · exact And.left
      · intro hy
        exact ⟨hy, hsub hy⟩
    rw [Finset.card_sdiff, hinter, hcard_img, Nat.card_Icc]
    omega
  obtain ⟨m, hmdeq⟩ := Finset.card_eq_one.mp hcompl
  have hmem : m ∈ Finset.Icc 1 S.card \ Finset.image
      (fun v : BdV (n := n) (k + 1) => (BdFin v).card) τ := by
    rw [hmdeq]
    exact Finset.mem_singleton_self m
  have hmIcc : m ∈ Finset.Icc 1 S.card := (Finset.mem_sdiff.mp hmem).1
  have hmnim : m ∉ Finset.image (fun v : BdV (n := n) (k + 1) => (BdFin v).card)
      τ := (Finset.mem_sdiff.mp hmem).2
  rw [Finset.mem_Icc] at hmIcc
  refine ⟨m, hmIcc.1, hmIcc.2, ?_, ?_⟩
  · intro v hv hcon
    apply hmnim
    exact Finset.mem_image.mpr ⟨v, hv, hcon⟩
  · intro m' hm1 hm2 hne2
    have hm'Icc : m' ∈ Finset.Icc 1 S.card := Finset.mem_Icc.mpr ⟨hm1, hm2⟩
    by_cases hm'im : m' ∈ Finset.image
      (fun v : BdV (n := n) (k + 1) => (BdFin v).card) τ
    · obtain ⟨v, hv, hvv⟩ := Finset.mem_image.mp hm'im
      exact ⟨v, hv, hvv⟩
    · have hsdiff : m' ∈ Finset.Icc 1 S.card \ Finset.image
          (fun v : BdV (n := n) (k + 1) => (BdFin v).card) τ :=
        Finset.mem_sdiff.mpr ⟨hm'Icc, hm'im⟩
      rw [hmdeq, Finset.mem_singleton] at hsdiff
      exact absurd hsdiff hne2

/-- An extension vertex has the missing card. -/
private lemma new_vertex_card {S : Finset (Fin (n + 1))} {k : ℕ}
    {τ : Finset (BdV (n := n) (k + 1))} (hτ : BdValid S (k + 1) τ)
    {m : ℕ} (_hm1 : 1 ≤ m) (_hm2 : m ≤ S.card)
    (_hmiss : ∀ v ∈ τ, (BdFin v).card ≠ m)
    (hall : ∀ m', 1 ≤ m' → m' ≤ S.card → m' ≠ m →
      ∃ v ∈ τ, (BdFin v).card = m')
    {d : BdV (n := n) (k + 1)} (hdvalid : BdValid S (k + 1) {d})
    (hdcomp : ∀ v ∈ τ, BdFin d ⊆ BdFin v ∨ BdFin v ⊆ BdFin d)
    (hdmem : d ∉ τ) :
    (BdFin d).card = m := by
  obtain ⟨hchain, hmem, hne⟩ := hτ
  obtain ⟨dchain, dmem, dne⟩ := hdvalid
  have hdset : BdValid S k (BdFin d) := dmem d (Finset.mem_singleton_self d)
  have hbd := card_of_valid hdset
  by_contra hne2
  obtain ⟨v, hv, hvv⟩ := hall _ hbd.1 hbd.2 hne2
  have hdv : d ≠ v := fun h => hdmem (h.symm ▸ hv)
  have hcomp := hdcomp v hv
  cases hcomp with
  | inl h =>
    have hss : BdFin d ⊂ BdFin v :=
      ⟨h, fun hle => hdv (Finset.Subset.antisymm h hle)⟩
    have hlt := Finset.card_lt_card hss
    omega
  | inr h =>
    have hss : BdFin v ⊂ BdFin d :=
      ⟨h, fun hle => hdv (Finset.Subset.antisymm h hle).symm⟩
    have hlt := Finset.card_lt_card hss
    omega

open Classical in
/-- Below-slot insertions: two extensions when card 1 is missing. -/
private lemma slot_below_two {S : Finset (Fin (n + 1))} {k : ℕ}
    {τ : Finset (BdV (n := n) (k + 1))} (hτ : BdValid S (k + 1) τ)
    (_hcard : τ.card = S.card - 1) (_hS : 2 ≤ S.card)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ S.card)
    (hmiss : ∀ v ∈ τ, (BdFin v).card ≠ m)
    (hall : ∀ m', 1 ≤ m' → m' ≤ S.card → m' ≠ m →
      ∃ v ∈ τ, (BdFin v).card = m')
    (hmeq : m = 1) :
    (Finset.univ.filter (fun d : BdV (n := n) (k + 1) =>
      d ∉ τ ∧ BdValid S (k + 1) {d} ∧
        ∀ v ∈ τ, BdFin d ⊆ BdFin v ∨ BdFin v ⊆ BdFin d)).card = 2 := by
  have hτcopy := hτ
  obtain ⟨hchain, hmem, hne⟩ := hτ
  obtain ⟨c2, hc2mem, hc2card⟩ := hall 2 (by omega) (by omega) (by omega)
  obtain ⟨x1, x2, hxne, hc2eq⟩ := Finset.card_eq_two.mp hc2card
  set d1 : BdV (n := n) (k + 1) := ({x1} : Finset (BdV (n := n) k)) with hd1
  set d2 : BdV (n := n) (k + 1) := ({x2} : Finset (BdV (n := n) k)) with hd2
  have hB1 : BdFin d1 = ({x1} : Finset (BdV (n := n) k)) := hd1
  have hB2 : BdFin d2 = ({x2} : Finset (BdV (n := n) k)) := hd2
  have hx1mem : x1 ∈ BdFin c2 := by
    rw [hc2eq]
    exact Finset.mem_insert_self x1 {x2}
  have hx2mem : x2 ∈ BdFin c2 := by
    rw [hc2eq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self x2)
  have hP : ∀ x ∈ BdFin c2, ∀ d : BdV (n := n) (k + 1),
      BdFin d = ({x} : Finset (BdV (n := n) k)) →
      d ∉ τ ∧ BdValid S (k + 1) {d} ∧
        ∀ v ∈ τ, BdFin d ⊆ BdFin v ∨ BdFin v ⊆ BdFin d := by
    intro x hxmem d hdB
    have hdcard : (BdFin d).card = 1 := by
      rw [hdB, Finset.card_singleton]
    refine ⟨?_, ?_, ?_⟩
    · intro hcon
      have hne2 := hmiss d hcon
      rw [hmeq] at hne2
      exact hne2 hdcard
    · refine ⟨?_, ?_, Finset.singleton_nonempty d⟩
      · intro a ha b hb
        rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
        subst a
        subst b
        exact Or.inl (Finset.Subset.refl _)
      · intro v hv
        rw [Finset.mem_singleton] at hv
        subst v
        have hset : BdValid S k (BdFin c2) := hmem c2 hc2mem
        have hsing := valid_singleton_of_mem hset hxmem
        change BdValid S k (BdFin d)
        rw [hdB]
        exact hsing
    · intro v hv
      have hcv := hchain c2 (Finset.mem_coe.mpr hc2mem) v
        (Finset.mem_coe.mpr hv)
      have hsub1 : BdFin d ⊆ BdFin c2 := by
        rw [hdB]
        intro y hy
        rw [Finset.mem_singleton] at hy
        subst y
        exact hxmem
      cases hcv with
      | inl h => exact Or.inl (hsub1.trans h)
      | inr h =>
        have hbd := card_mem_valid hτcopy hv
        have hnem : (BdFin v).card ≠ m := hmiss v hv
        rw [hmeq] at hnem
        have hle := Finset.card_le_card h
        rw [hc2card] at hle
        have hcardv : (BdFin v).card = 2 := by omega
        have heq : BdFin v = BdFin c2 :=
          Finset.eq_of_subset_of_card_le h (by omega)
        rw [heq]
        exact Or.inl hsub1
  have hVeq : Finset.univ.filter (fun d : BdV (n := n) (k + 1) =>
        d ∉ τ ∧ BdValid S (k + 1) {d} ∧
          ∀ v ∈ τ, BdFin d ⊆ BdFin v ∨ BdFin v ⊆ BdFin d) =
      {d1, d2} := by
    ext d
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      obtain ⟨-, hdτ, hdvalid, hdcomp⟩ := h
      have hdm := new_vertex_card hτcopy hm1 hm2 hmiss hall hdvalid hdcomp hdτ
      rw [hmeq] at hdm
      obtain ⟨x, hxeq⟩ := Finset.card_eq_one.mp hdm
      have hcomp2 := hdcomp c2 hc2mem
      have hxmem : x ∈ BdFin c2 := by
        cases hcomp2 with
        | inl h =>
          have hx : x ∈ BdFin d := by
            rw [hxeq]
            exact Finset.mem_singleton_self x
          exact h hx
        | inr h =>
          exfalso
          have hle := Finset.card_le_card h
          rw [hxeq, Finset.card_singleton, hc2card] at hle
          omega
      rw [hc2eq, Finset.mem_insert, Finset.mem_singleton] at hxmem
      cases hxmem with
      | inl h =>
        subst x
        left
        have hBeq : BdFin d = BdFin d1 := by rw [hxeq, hB1]
        exact hBeq
      | inr h =>
        subst x
        right
        have hBeq : BdFin d = BdFin d2 := by rw [hxeq, hB2]
        exact hBeq
    · intro h
      rcases h with h | h
      · subst d
        obtain ⟨hd1τ, hd1valid, hd1comp⟩ := hP x1 hx1mem d1 hB1
        exact ⟨Finset.mem_univ d1, hd1τ, hd1valid, hd1comp⟩
      · subst d
        obtain ⟨hd2τ, hd2valid, hd2comp⟩ := hP x2 hx2mem d2 hB2
        exact ⟨Finset.mem_univ d2, hd2τ, hd2valid, hd2comp⟩
  have hdne : d1 ≠ d2 := by
    intro hcon
    have hB : BdFin d1 = BdFin d2 := by rw [hcon]
    rw [hB1, hB2] at hB
    exact hxne (Finset.singleton_injective hB)
  rw [hVeq, Finset.card_pair hdne]

/-- Nonempty subsets of valid sets are valid (subchains). -/
private lemma valid_subset_of_valid {S : Finset (Fin (n + 1))} :
    ∀ {k} {c d : Finset (BdV (n := n) k)},
      BdValid S k c → d ⊆ c → d.Nonempty → BdValid S k d := by
  intro k
  induction k with
  | zero =>
    intro c d hc hsub hne
    exact ⟨hsub.trans hc.1, hne⟩
  | succ k ih =>
    intro c d hc hsub hne
    obtain ⟨cchain, cmem, cne⟩ := hc
    refine ⟨?_, ?_, hne⟩
    · intro a ha b hb
      have ha' := Finset.mem_coe.mpr (hsub (Finset.mem_coe.mp ha))
      have hb' := Finset.mem_coe.mpr (hsub (Finset.mem_coe.mp hb))
      exact cchain a ha' b hb'
    · intro w hw
      exact cmem w (hsub hw)

open Classical in
/-- Between-slot insertions: two extensions when an interior card is missing. -/
private lemma slot_between_two {S : Finset (Fin (n + 1))} {k : ℕ}
    {τ : Finset (BdV (n := n) (k + 1))} (hτ : BdValid S (k + 1) τ)
    (_hcard : τ.card = S.card - 1) (_hS : 2 ≤ S.card)
    {m : ℕ} (hm1 : 1 ≤ m) (hm2 : m ≤ S.card)
    (hmiss : ∀ v ∈ τ, (BdFin v).card ≠ m)
    (hall : ∀ m', 1 ≤ m' → m' ≤ S.card → m' ≠ m →
      ∃ v ∈ τ, (BdFin v).card = m')
    (hmlo : 2 ≤ m) (hmhi : m ≤ S.card - 1) :
    (Finset.univ.filter (fun d : BdV (n := n) (k + 1) =>
      d ∉ τ ∧ BdValid S (k + 1) {d} ∧
        ∀ v ∈ τ, BdFin d ⊆ BdFin v ∨ BdFin v ⊆ BdFin d)).card = 2 := by
  have hτcopy := hτ
  obtain ⟨hchain, hmem, hne⟩ := hτ
  obtain ⟨clo, hloMem, hloCard⟩ := hall (m - 1) (by omega) (by omega) (by omega)
  obtain ⟨chi, hhiMem, hhiCard⟩ := hall (m + 1) (by omega) (by omega) (by omega)
  have hloSub : BdFin clo ⊂ BdFin chi := by
    have hcomp := hchain clo (Finset.mem_coe.mpr hloMem) chi
      (Finset.mem_coe.mpr hhiMem)
    cases hcomp with
    | inl h =>
      refine ⟨h, fun hle => ?_⟩
      have hle2 := Finset.card_le_card hle
      omega
    | inr h =>
      exfalso
      have hle := Finset.card_le_card h
      omega
  have hgap2 : (BdFin chi \ BdFin clo).card = 2 := by
    have hinter : BdFin clo ∩ BdFin chi = BdFin clo := by
      ext y
      simp only [Finset.mem_inter]
      constructor
      · exact And.left
      · intro hy
        exact ⟨hy, hloSub.1 hy⟩
    rw [Finset.card_sdiff, hinter, hloCard, hhiCard]
    omega
  obtain ⟨x1, x2, hxne, hxeq⟩ := Finset.card_eq_two.mp hgap2
  set d1 : BdV (n := n) (k + 1) := (insert x1 (BdFin clo) :
    Finset (BdV (n := n) k)) with hd1
  set d2 : BdV (n := n) (k + 1) := (insert x2 (BdFin clo) :
    Finset (BdV (n := n) k)) with hd2
  have hB1 : BdFin d1 = insert x1 (BdFin clo) := hd1
  have hB2 : BdFin d2 = insert x2 (BdFin clo) := hd2
  have hx1mem : x1 ∈ BdFin chi \ BdFin clo := by
    rw [hxeq]
    exact Finset.mem_insert_self x1 {x2}
  have hx2mem : x2 ∈ BdFin chi \ BdFin clo := by
    rw [hxeq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self x2)
  have hx1hi : x1 ∈ BdFin chi := (Finset.mem_sdiff.mp hx1mem).1
  have hx1lo : x1 ∉ BdFin clo := (Finset.mem_sdiff.mp hx1mem).2
  have hx2hi : x2 ∈ BdFin chi := (Finset.mem_sdiff.mp hx2mem).1
  have hx2lo : x2 ∉ BdFin clo := (Finset.mem_sdiff.mp hx2mem).2
  have hP : ∀ x ∈ BdFin chi \ BdFin clo, ∀ d : BdV (n := n) (k + 1),
      BdFin d = insert x (BdFin clo) →
      d ∉ τ ∧ BdValid S (k + 1) {d} ∧
        ∀ v ∈ τ, BdFin d ⊆ BdFin v ∨ BdFin v ⊆ BdFin d := by
    intro x hxmem d hdB
    have hxhi : x ∈ BdFin chi := (Finset.mem_sdiff.mp hxmem).1
    have hxlo : x ∉ BdFin clo := (Finset.mem_sdiff.mp hxmem).2
    have hdcard : (BdFin d).card = m := by
      rw [hdB, Finset.card_insert_of_notMem hxlo, hloCard]
      omega
    have hdsub_hi : BdFin d ⊆ BdFin chi := by
      rw [hdB]
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · exact hxhi
      · exact hloSub.1 hy
    have hlo_sub_d : BdFin clo ⊂ BdFin d := by
      refine ⟨?_, ?_⟩
      · rw [hdB]
        exact Finset.subset_insert x (BdFin clo)
      · intro hle
        have hle2 := Finset.card_le_card hle
        rw [hdcard, hloCard] at hle2
        omega
    refine ⟨?_, ?_, ?_⟩
    · intro hcon
      exact hmiss d hcon hdcard
    · refine ⟨?_, ?_, ?_⟩
      · intro a ha b hb
        rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
        subst a
        subst b
        exact Or.inl (Finset.Subset.refl _)
      · intro v hv
        rw [Finset.mem_singleton] at hv
        subst v
        change BdValid S k (BdFin d)
        have hchi : BdValid S k (BdFin chi) := hmem chi hhiMem
        have hne2 : (BdFin d).Nonempty := by
          have hlov : BdValid S k (BdFin clo) := hmem clo hloMem
          have hclo := nonempty_of_valid hlov
          obtain ⟨w, hw⟩ := hclo
          exact ⟨w, hlo_sub_d.1 hw⟩
        exact valid_subset_of_valid hchi hdsub_hi hne2
      · exact Finset.singleton_nonempty d
    · intro v hv
      have hbd := card_mem_valid hτcopy hv
      have hnem : (BdFin v).card ≠ m := hmiss v hv
      by_cases hle : (BdFin v).card ≤ m - 1
      · -- below: v ⊆ clo ⊆ d
        have hvc := hchain v (Finset.mem_coe.mpr hv) clo
          (Finset.mem_coe.mpr hloMem)
        have hsub : BdFin v ⊆ BdFin clo := by
          cases hvc with
          | inl h => exact h
          | inr h =>
            have hle2 := Finset.card_le_card h
            rw [hloCard] at hle2
            have heq : BdFin clo = BdFin v :=
              Finset.eq_of_subset_of_card_le h (by omega)
            rw [heq]
        have hsubd : BdFin clo ⊆ BdFin d := hlo_sub_d.1
        exact Or.inr (hsub.trans hsubd)
      · -- above: d ⊆ chi ⊆ v
        have hge : m + 1 ≤ (BdFin v).card := by omega
        have hvc := hchain v (Finset.mem_coe.mpr hv) chi
          (Finset.mem_coe.mpr hhiMem)
        have hsub : BdFin chi ⊆ BdFin v := by
          cases hvc with
          | inl h =>
            have hle2 := Finset.card_le_card h
            rw [hhiCard] at hle2
            have heq : BdFin v = BdFin chi :=
              Finset.eq_of_subset_of_card_le h (by omega)
            rw [heq]
          | inr h => exact h
        exact Or.inl (hdsub_hi.trans hsub)
  have hVeq : Finset.univ.filter (fun d : BdV (n := n) (k + 1) =>
        d ∉ τ ∧ BdValid S (k + 1) {d} ∧
          ∀ v ∈ τ, BdFin d ⊆ BdFin v ∨ BdFin v ⊆ BdFin d) =
      {d1, d2} := by
    ext d
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      obtain ⟨-, hdτ, hdvalid, hdcomp⟩ := h
      have hdm := new_vertex_card hτcopy hm1 hm2 hmiss hall hdvalid hdcomp hdτ
      have hdlo : BdFin clo ⊂ BdFin d := by
        have hcomp := hdcomp clo hloMem
        cases hcomp with
        | inl h =>
          exfalso
          have hle := Finset.card_le_card h
          rw [hdm, hloCard] at hle
          omega
        | inr h =>
          refine ⟨h, fun hle => ?_⟩
          have hle2 := Finset.card_le_card hle
          rw [hdm, hloCard] at hle2
          omega
      have hdhi : BdFin d ⊂ BdFin chi := by
        have hcomp := hdcomp chi hhiMem
        cases hcomp with
        | inl h =>
          refine ⟨h, fun hle => ?_⟩
          have hle2 := Finset.card_le_card hle
          rw [hdm, hhiCard] at hle2
          omega
        | inr h =>
          exfalso
          have hle := Finset.card_le_card h
          rw [hdm, hhiCard] at hle
          omega
      have hdiff1 : (BdFin d \ BdFin clo).card = 1 := by
        have hinter : BdFin clo ∩ BdFin d = BdFin clo := by
          ext y
          simp only [Finset.mem_inter]
          constructor
          · exact And.left
          · intro hy
            exact ⟨hy, hdlo.1 hy⟩
        rw [Finset.card_sdiff, hinter, hdm, hloCard]
        omega
      obtain ⟨x, hxdif⟩ := Finset.card_eq_one.mp hdiff1
      have hxmemd : x ∈ BdFin d \ BdFin clo := by
        rw [hxdif]
        exact Finset.mem_singleton_self x
      have hxd : x ∈ BdFin d := (Finset.mem_sdiff.mp hxmemd).1
      have hxlo : x ∉ BdFin clo := (Finset.mem_sdiff.mp hxmemd).2
      have hxhi : x ∈ BdFin chi := hdhi.1 hxd
      have hxgap : x ∈ BdFin chi \ BdFin clo :=
        Finset.mem_sdiff.mpr ⟨hxhi, hxlo⟩
      have hderase : BdFin d \ {x} = BdFin clo := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_singleton]
        constructor
        · intro h
          obtain ⟨hyd, hyne⟩ := h
          by_contra hylo
          have hmem2 : y ∈ BdFin d \ BdFin clo :=
            Finset.mem_sdiff.mpr ⟨hyd, hylo⟩
          rw [hxdif, Finset.mem_singleton] at hmem2
          exact hyne hmem2
        · intro hy
          exact ⟨hdlo.1 hy, fun hcon => hxlo (hcon ▸ hy)⟩
      have hdB : BdFin d = insert x (BdFin clo) := by
        ext y
        rw [Finset.mem_insert]
        constructor
        · intro hyd
          by_cases hyeq : y = x
          · exact Or.inl hyeq
          · right
            have hnot : y ∉ ({x} : Finset (BdV (n := n) k)) := by
              rw [Finset.mem_singleton]
              exact hyeq
            have hmem2 : y ∈ BdFin d \ {x} :=
              Finset.mem_sdiff.mpr ⟨hyd, hnot⟩
            rw [hderase] at hmem2
            exact hmem2
        · intro h
          rcases h with h | h
          · subst y
            exact hxd
          · exact hdlo.1 h
      rw [hxeq, Finset.mem_insert, Finset.mem_singleton] at hxgap
      cases hxgap with
      | inl h =>
        subst x
        left
        have hBeq : BdFin d = BdFin d1 := by rw [hdB, hB1]
        exact hBeq
      | inr h =>
        subst x
        right
        have hBeq : BdFin d = BdFin d2 := by rw [hdB, hB2]
        exact hBeq
    · intro h
      rcases h with h | h
      · subst d
        obtain ⟨hd1τ, hd1valid, hd1comp⟩ := hP x1 hx1mem d1 hB1
        exact ⟨Finset.mem_univ d1, hd1τ, hd1valid, hd1comp⟩
      · subst d
        obtain ⟨hd2τ, hd2valid, hd2comp⟩ := hP x2 hx2mem d2 hB2
        exact ⟨Finset.mem_univ d2, hd2τ, hd2valid, hd2comp⟩
  have hdne : d1 ≠ d2 := by
    intro hcon
    have hB : BdFin d1 = BdFin d2 := by rw [hcon]
    rw [hB1, hB2] at hB
    have hmem : x1 ∈ insert x2 (BdFin clo) := by
      rw [← hB]
      exact Finset.mem_insert_self x1 (BdFin clo)
    rw [Finset.mem_insert] at hmem
    cases hmem with
    | inl h => exact hxne h
    | inr h => exact hx1lo h
  rw [hVeq, Finset.card_pair hdne]

/-- Consecutive card sets cover exactly `Icc 1 (|S|-1)`. -/
private lemma consec_cards {S : Finset (Fin (n + 1))} {k : ℕ}
    {c : Finset (BdV (n := n) (k + 1))} (hc : BdValid S (k + 1) c)
    (hcard : c.card = S.card - 1)
    (hconsec : ∀ m', 1 ≤ m' → m' ≤ S.card - 1 →
      ∃ u ∈ c, (BdFin u).card = m') :
    Finset.image (fun v : BdV (n := n) (k + 1) => (BdFin v).card) c =
      Finset.Icc 1 (S.card - 1) := by
  obtain ⟨hchain, hmem, hne⟩ := hc
  have hinj : Set.InjOn (fun v : BdV (n := n) (k + 1) => (BdFin v).card)
      ↑c := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    have hab' : (BdFin a).card = (BdFin b).card := hab
    by_contra hne2
    exact cards_ne_of_ne hchain ha hb hne2 hab'
  have hsup : Finset.Icc 1 (S.card - 1) ⊆
      Finset.image (fun v : BdV (n := n) (k + 1) => (BdFin v).card) c := by
    intro m' hm'
    rw [Finset.mem_Icc] at hm'
    obtain ⟨u, hu, hucard⟩ := hconsec m' hm'.1 hm'.2
    exact Finset.mem_image.mpr ⟨u, hu, hucard⟩
  have hcard_img : (Finset.image
      (fun v : BdV (n := n) (k + 1) => (BdFin v).card) c).card =
      (Finset.Icc 1 (S.card - 1)).card := by
    rw [Finset.card_image_of_injOn hinj, hcard, Nat.card_Icc]
    omega
  exact (Finset.eq_of_subset_of_card_le hsup (le_of_eq hcard_img)).symm

/-- A strict super/subset pair differing by one card is an insertion. -/
private lemma insert_of_ssubset_card {α : Type*} [DecidableEq α]
    {s t : Finset α} (hsub : s ⊂ t) (hcard : t.card = s.card + 1) :
    ∃ x ∉ s, t = insert x s := by
  have hdiff : (t \ s).card = 1 := by
    have hinter : s ∩ t = s := by
      ext y
      simp only [Finset.mem_inter]
      constructor
      · exact And.left
      · intro hy
        exact ⟨hy, hsub.1 hy⟩
    rw [Finset.card_sdiff, hinter, hcard]
    omega
  obtain ⟨x, hxeq⟩ := Finset.card_eq_one.mp hdiff
  have hxmem : x ∈ t \ s := by
    rw [hxeq]
    exact Finset.mem_singleton_self x
  have hxt : x ∈ t := (Finset.mem_sdiff.mp hxmem).1
  have hxs : x ∉ s := (Finset.mem_sdiff.mp hxmem).2
  refine ⟨x, hxs, ?_⟩
  ext y
  rw [Finset.mem_insert]
  constructor
  · intro hyt
    by_cases hyeq : y = x
    · exact Or.inl hyeq
    · right
      by_contra hys
      have hmem2 : y ∈ t \ s := Finset.mem_sdiff.mpr ⟨hyt, hys⟩
      rw [hxeq, Finset.mem_singleton] at hmem2
      exact hyeq hmem2
  · intro h
    rcases h with h | h
    · subst y
      exact hxt
    · exact hsub.1 h

/-- For consecutive chains, the support union is the max element's support. -/
private lemma union_eq_max_consec {S : Finset (Fin (n + 1))} {k : ℕ}
    {c : Finset (BdV (n := n) (k + 1))} (hc : BdValid S (k + 1) c)
    (hcards : Finset.image (fun v : BdV (n := n) (k + 1) => (BdFin v).card)
      c = Finset.Icc 1 (S.card - 1))
    {umax : BdV (n := n) (k + 1)} (humem : umax ∈ c)
    (hucard : (BdFin umax).card = S.card - 1) :
    BdSuppSet (k + 1) c = BdSupp (k + 1) umax := by
  obtain ⟨hchain, hmem, hne⟩ := hc
  apply Finset.Subset.antisymm
  · intro j hj
    rw [mem_BdSuppSet] at hj
    obtain ⟨v, hvc, hjv⟩ := hj
    have hsub : BdFin v ⊆ BdFin umax := by
      have hcomp := hchain v (Finset.mem_coe.mpr hvc) umax
        (Finset.mem_coe.mpr humem)
      cases hcomp with
      | inl h => exact h
      | inr h =>
        have hmem2 : (BdFin v).card ∈ Finset.Icc 1 (S.card - 1) := by
          rw [← hcards]
          exact Finset.mem_image.mpr ⟨v, hvc, rfl⟩
        rw [Finset.mem_Icc] at hmem2
        have hle := Finset.card_le_card h
        rw [hucard] at hle
        have heq : BdFin umax = BdFin v :=
          Finset.eq_of_subset_of_card_le h (by omega)
        rw [heq]
    exact BdSupp_mono_succ hsub hjv
  · intro j hj
    rw [mem_BdSuppSet]
    exact ⟨umax, humem, hj⟩

open Classical in
/-- Slot count over consecutive chains, by level induction. -/
private lemma consec_slot_count {S : Finset (Fin (n + 1))} (hS : 2 ≤ S.card) :
    ∀ (j : ℕ) (c : Finset (BdV (n := n) (j + 1))),
      BdValid S (j + 1) c → c.card = S.card - 1 →
      (∀ m', 1 ≤ m' → m' ≤ S.card - 1 → ∃ u ∈ c, (BdFin u).card = m') →
      (BdSuppSet (j + 1) c = S →
        (Finset.univ.filter (fun x : BdV (n := n) (j + 1) =>
          x ∉ c ∧ BdValid S (j + 1) {x} ∧
            ∀ w ∈ c, BdFin x ⊆ BdFin w ∨ BdFin w ⊆ BdFin x)).card = 2) ∧
      (BdSuppSet (j + 1) c ≠ S →
        (Finset.univ.filter (fun x : BdV (n := n) (j + 1) =>
          x ∉ c ∧ BdValid S (j + 1) {x} ∧
            ∀ w ∈ c, BdFin x ⊆ BdFin w ∨ BdFin w ⊆ BdFin x)).card = 1) := by
  intro j
  induction j with
  | zero =>
    intro c hc hcard hconsec
    have hτcopy := hc
    obtain ⟨hchain, hmem, hne⟩ := hc
    obtain ⟨umax, humem, hucard⟩ := hconsec (S.card - 1) (by omega) le_rfl
    have hcards := consec_cards hτcopy hcard hconsec
    have hunion : BdSuppSet 1 c = BdSupp 1 umax :=
      union_eq_max_consec hτcopy hcards humem hucard
    have humax_sub : BdFin umax ⊆ S := (hmem umax humem).1
    have hne_union : BdSuppSet 1 c ≠ S := by
      rw [hunion]
      intro hcon
      have hcardu : (BdSupp 1 umax).card ≤ S.card - 1 := by
        have h1 : (BdSupp 1 umax).card ≤
            ∑ i ∈ BdFin umax, (BdSupp 0 i).card := by
          change ((BdFin umax).biUnion (BdSupp 0)).card ≤ _
          exact Finset.card_biUnion_le
        have h2 : ∑ i ∈ BdFin umax, (BdSupp 0 i).card = (BdFin umax).card := by
          rw [Finset.sum_congr rfl (fun i hi => by
            change (({BdFin0 i} : Finset (Fin (n + 1)))).card = 1
            exact Finset.card_singleton _)]
          simp
        omega
      have hcc := congrArg Finset.card hcon
      omega
    have hcompl : ((S \ BdFin umax : Finset (BdV (n := n) 0))).card = 1 := by
      have hinter : (BdFin umax ∩ S : Finset (BdV (n := n) 0)) = BdFin umax := by
        ext y
        constructor
        · intro h
          exact (Finset.mem_inter.mp h).1
        · intro hy
          exact Finset.mem_inter.mpr ⟨hy, humax_sub hy⟩
      have hsd : ((S \ BdFin umax : Finset (BdV (n := n) 0))).card =
          S.card - ((BdFin umax ∩ S : Finset (BdV (n := n) 0))).card :=
        Finset.card_sdiff
      have hcc : ((BdFin umax ∩ S : Finset (BdV (n := n) 0))).card =
          (BdFin umax).card := congrArg Finset.card hinter
      omega
    obtain ⟨z0, hz0eq⟩ := Finset.card_eq_one.mp hcompl
    have hz0mem : z0 ∈ (S \ BdFin umax : Finset (BdV (n := n) 0)) := by
      rw [hz0eq]
      exact Finset.mem_singleton_self z0
    have hz0S : z0 ∈ S := (Finset.mem_sdiff.mp hz0mem).1
    have hz0u : z0 ∉ BdFin umax := (Finset.mem_sdiff.mp hz0mem).2
    set x0 : BdV (n := n) 1 :=
      (insert z0 (BdFin umax) : Finset (BdV (n := n) 0)) with hx0
    have hB0 : BdFin x0 = insert z0 (BdFin umax) := hx0
    have hx0card : (BdFin x0).card = S.card := by
      rw [hB0, Finset.card_insert_of_notMem hz0u, hucard]
      omega
    have hmissS : ∀ v ∈ c, (BdFin v).card ≠ S.card := by
      intro v hv hcon
      have hmem2 : (BdFin v).card ∈ Finset.Icc 1 (S.card - 1) := by
        rw [← hcards]
        exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
      rw [Finset.mem_Icc] at hmem2
      omega
    have hallS : ∀ m', 1 ≤ m' → m' ≤ S.card → m' ≠ S.card →
        ∃ v ∈ c, (BdFin v).card = m' := by
      intro m' hm1' hm2' hne2
      have hmle : m' ≤ S.card - 1 := by omega
      exact hconsec m' hm1' hmle
    have hVeq : Finset.univ.filter (fun x : BdV (n := n) 1 =>
          x ∉ c ∧ BdValid S 1 {x} ∧
            ∀ w ∈ c, BdFin x ⊆ BdFin w ∨ BdFin w ⊆ BdFin x) = {x0} := by
      ext x
      rw [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro h
        obtain ⟨-, hxτ, hxvalid, hxcomp⟩ := h
        have hxcard := new_vertex_card hτcopy (by omega : 1 ≤ S.card)
          le_rfl hmissS hallS hxvalid hxcomp hxτ
        have hxsup : BdFin umax ⊂ BdFin x := by
          have hcomp := hxcomp umax humem
          cases hcomp with
          | inl h =>
            exfalso
            have hle := Finset.card_le_card h
            rw [hxcard, hucard] at hle
            omega
          | inr h =>
            refine ⟨h, fun hle => ?_⟩
            have hle2 := Finset.card_le_card hle
            rw [hxcard, hucard] at hle2
            omega
        have hcardx : (BdFin x).card = (BdFin umax).card + 1 := by
          rw [hxcard, hucard]
          omega
        obtain ⟨z, hzs, hxB⟩ := insert_of_ssubset_card hxsup hcardx
        have hxz : z ∈ (S \ BdFin umax : Finset (BdV (n := n) 0)) := by
          have hxd : z ∈ BdFin x := by
            rw [hxB]
            exact Finset.mem_insert_self z (BdFin umax)
          have hxsub : BdFin x ⊆ S := by
            have hxv : BdValid S 0 (BdFin x) := by
              obtain ⟨xc, xm, xn⟩ := hxvalid
              exact xm x (Finset.mem_singleton_self x)
            exact hxv.1
          exact Finset.mem_sdiff.mpr ⟨hxsub hxd, hzs⟩
        rw [hz0eq, Finset.mem_singleton] at hxz
        subst z
        have hBeq : BdFin x = BdFin x0 := by rw [hxB, hB0]
        exact hBeq
      · intro h
        subst x
        refine ⟨Finset.mem_univ x0, ?_, ?_, ?_⟩
        · intro hcon
          exact hmissS x0 hcon hx0card
        · refine ⟨?_, ?_, Finset.singleton_nonempty x0⟩
          · intro a ha b hb
            rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
            subst a
            subst b
            exact Or.inl (Finset.Subset.refl _)
          · intro v hv
            rw [Finset.mem_singleton] at hv
            subst v
            change BdValid S 0 (BdFin x0)
            rw [hB0]
            refine ⟨?_, ?_⟩
            · intro y hy
              rw [Finset.mem_insert] at hy
              rcases hy with rfl | hy
              · exact hz0S
              · exact humax_sub hy
            · exact ⟨z0, Finset.mem_insert_self z0 (BdFin umax)⟩
        · intro e he
          have hec := hchain e (Finset.mem_coe.mpr he) umax
            (Finset.mem_coe.mpr humem)
          have hsub : BdFin e ⊆ BdFin umax := by
            cases hec with
            | inl h => exact h
            | inr h =>
              have hmem2 : (BdFin e).card ∈ Finset.Icc 1 (S.card - 1) := by
                rw [← hcards]
                exact Finset.mem_image.mpr ⟨e, he, rfl⟩
              rw [Finset.mem_Icc] at hmem2
              have hle := Finset.card_le_card h
              rw [hucard] at hle
              have heq : BdFin umax = BdFin e :=
                Finset.eq_of_subset_of_card_le h (by omega)
              rw [heq]
          have hsubx : BdFin umax ⊆ BdFin x0 := by
            rw [hB0]
            exact Finset.subset_insert z0 (BdFin umax)
          exact Or.inr (hsub.trans hsubx)
    refine ⟨?_, ?_⟩
    · intro hcon
      exact absurd hcon hne_union
    · intro _
      rw [hVeq, Finset.card_singleton]
  | succ j ih =>
    intro c hc hcard hconsec
    have hτcopy := hc
    obtain ⟨hchain, hmem, hne⟩ := hc
    obtain ⟨umax, humem, hucard⟩ := hconsec (S.card - 1) (by omega) le_rfl
    have hcards := consec_cards hτcopy hcard hconsec
    have hunion : BdSuppSet (j + 2) c = BdSupp (j + 2) umax :=
      union_eq_max_consec hτcopy hcards humem hucard
    have hmissS : ∀ v ∈ c, (BdFin v).card ≠ S.card := by
      intro v hv hcon
      have hmem2 : (BdFin v).card ∈ Finset.Icc 1 (S.card - 1) := by
        rw [← hcards]
        exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
      rw [Finset.mem_Icc] at hmem2
      omega
    have hallS : ∀ m', 1 ≤ m' → m' ≤ S.card → m' ≠ S.card →
        ∃ v ∈ c, (BdFin v).card = m' := by
      intro m' hm1' hm2' hne2
      have hmle : m' ≤ S.card - 1 := by omega
      exact hconsec m' hm1' hmle
    have humax_valid : BdValid S (j + 1) (BdFin umax) := hmem umax humem
    -- vertex count equals z-count over BdFin umax
    have hVeq : Finset.univ.filter (fun x : BdV (n := n) (j + 2) =>
          x ∉ c ∧ BdValid S (j + 2) {x} ∧
            ∀ w ∈ c, BdFin x ⊆ BdFin w ∨ BdFin w ⊆ BdFin x) =
        (Finset.univ.filter (fun z : BdV (n := n) (j + 1) =>
          z ∉ BdFin umax ∧ BdValid S (j + 1) {z} ∧
            ∀ w ∈ BdFin umax,
              BdFin z ⊆ BdFin w ∨ BdFin w ⊆ BdFin z)).image
          ((fun z : BdV (n := n) (j + 1) =>
            (insert z (BdFin umax) : Finset (BdV (n := n) (j + 1)))) :
            BdV (n := n) (j + 1) → BdV (n := n) (j + 2)) := by
      ext x
      rw [Finset.mem_filter]
      constructor
      · intro h
        obtain ⟨-, hxτ, hxvalid, hxcomp⟩ := h
        have hxcard := new_vertex_card hτcopy (by omega : 1 ≤ S.card)
          le_rfl hmissS hallS hxvalid hxcomp hxτ
        have hxsup : BdFin umax ⊂ BdFin x := by
          have hcomp := hxcomp umax humem
          cases hcomp with
          | inl h =>
            exfalso
            have hle := Finset.card_le_card h
            rw [hxcard, hucard] at hle
            omega
          | inr h =>
            refine ⟨h, fun hle => ?_⟩
            have hle2 := Finset.card_le_card hle
            rw [hxcard, hucard] at hle2
            omega
        have hcardx : (BdFin x).card = (BdFin umax).card + 1 := by
          rw [hxcard, hucard]
          omega
        obtain ⟨z, hzs, hxB⟩ := insert_of_ssubset_card hxsup hcardx
        have hxv : BdValid S (j + 1) (BdFin x) := by
          obtain ⟨xc, xm, xn⟩ := hxvalid
          exact xm x (Finset.mem_singleton_self x)
        refine Finset.mem_image.mpr ⟨z, ?_, hxB.symm⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ z, hzs, ?_, ?_⟩
        · have hzx : z ∈ BdFin x := by
            rw [hxB]
            exact Finset.mem_insert_self z (BdFin umax)
          exact valid_singleton_of_mem hxv hzx
        · intro w hw
          obtain ⟨xchain, xmem, xne⟩ := hxv
          have hzx : z ∈ BdFin x := by
            rw [hxB]
            exact Finset.mem_insert_self z (BdFin umax)
          have hwx : w ∈ BdFin x := by
            rw [hxB]
            exact Finset.mem_insert_of_mem hw
          exact xchain z (Finset.mem_coe.mpr hzx) w (Finset.mem_coe.mpr hwx)
      · intro h
        obtain ⟨z, hzV, hxB⟩ := Finset.mem_image.mp h
        rw [Finset.mem_filter] at hzV
        obtain ⟨-, hzs, hzvalid, hzcomp⟩ := hzV
        refine ⟨Finset.mem_univ x, ?_, ?_, ?_⟩
        · intro hcon
          have hxcard : (BdFin x).card = S.card := by
            have hBeq : BdFin x = insert z (BdFin umax) := hxB.symm
            rw [hBeq, Finset.card_insert_of_notMem hzs, hucard]
            omega
          exact hmissS x hcon hxcard
        · -- validity of {x}: BdFin x = insert z umax is a valid chain
          have hBeq : BdFin x = insert z (BdFin umax) := hxB.symm
          have hchainx : ∀ a ∈ ((BdFin x : Finset (BdV (n := n) (j + 1))) :
              Set (BdV (n := n) (j + 1))), ∀ b ∈
              ((BdFin x : Finset (BdV (n := n) (j + 1))) :
              Set (BdV (n := n) (j + 1))),
              BdFin a ⊆ BdFin b ∨ BdFin b ⊆ BdFin a := by
            intro a ha b hb
            rw [hBeq, Finset.mem_coe, Finset.mem_insert] at ha hb
            rcases ha with ha | ha <;> rcases hb with hb | hb
            · subst a
              subst b
              exact Or.inl (Finset.Subset.refl _)
            · subst a
              exact hzcomp b hb
            · subst b
              exact (hzcomp a ha).symm
            · obtain ⟨uchain, umem, une⟩ := humax_valid
              exact uchain a (Finset.mem_coe.mpr ha) b (Finset.mem_coe.mpr hb)
          have hmemx : ∀ v ∈ BdFin x, BdValid S j v := by
            intro v hv
            rw [hBeq, Finset.mem_insert] at hv
            rcases hv with hv | hv
            · subst v
              obtain ⟨zc, zm, zn⟩ := hzvalid
              exact zm z (Finset.mem_singleton_self z)
            · obtain ⟨uchain, umem, une⟩ := humax_valid
              exact umem v hv
          have hnex : (BdFin x).Nonempty := by
            rw [hBeq]
            exact ⟨z, Finset.mem_insert_self z (BdFin umax)⟩
          -- assemble BdValid S (j+2) {x} from components
          change BdValid S (j + 1 + 1) ({x} : Finset (BdV (n := n) (j + 1 + 1)))
          refine ⟨?_, ?_, Finset.singleton_nonempty x⟩
          · intro a ha b hb
            rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
            subst a
            subst b
            exact Or.inl (Finset.Subset.refl _)
          · intro v hv
            rw [Finset.mem_singleton] at hv
            subst v
            change BdValid S (j + 1) (BdFin x)
            exact ⟨hchainx, hmemx, hnex⟩
        · intro e he
          have hec := hchain e (Finset.mem_coe.mpr he) umax
            (Finset.mem_coe.mpr humem)
          have hsub : BdFin e ⊆ BdFin umax := by
            cases hec with
            | inl h => exact h
            | inr h =>
              have hmem2 : (BdFin e).card ∈ Finset.Icc 1 (S.card - 1) := by
                rw [← hcards]
                exact Finset.mem_image.mpr ⟨e, he, rfl⟩
              rw [Finset.mem_Icc] at hmem2
              have hle := Finset.card_le_card h
              rw [hucard] at hle
              have heq : BdFin umax = BdFin e :=
                Finset.eq_of_subset_of_card_le h (by omega)
              rw [heq]
          have hBeq : BdFin x = insert z (BdFin umax) := hxB.symm
          have hsubx : BdFin umax ⊆ BdFin x := by
            rw [hBeq]
            exact Finset.subset_insert z (BdFin umax)
          exact Or.inr (hsub.trans hsubx)
    have hinjZ : Set.InjOn
        ((fun z : BdV (n := n) (j + 1) =>
          (insert z (BdFin umax) : Finset (BdV (n := n) (j + 1)))) :
          BdV (n := n) (j + 1) → BdV (n := n) (j + 2))
        ↑(Finset.univ.filter (fun z : BdV (n := n) (j + 1) =>
          z ∉ BdFin umax ∧ BdValid S (j + 1) {z} ∧
            ∀ w ∈ BdFin umax,
              BdFin z ⊆ BdFin w ∨ BdFin w ⊆ BdFin z)) := by
      intro z1 hz1 z2 hz2 heq
      rw [Finset.mem_coe, Finset.mem_filter] at hz1 hz2
      obtain ⟨-, hz1u, -, -⟩ := hz1
      have heq' : insert z1 (BdFin umax) = insert z2 (BdFin umax) := heq
      have hmem : z1 ∈ insert z2 (BdFin umax) := by
        rw [← heq']
        exact Finset.mem_insert_self z1 (BdFin umax)
      rw [Finset.mem_insert] at hmem
      cases hmem with
      | inl h => exact h
      | inr h => exact absurd h hz1u
    obtain ⟨m', hm1', hm2', hmiss', hall'⟩ :=
      missing_card_exists humax_valid hucard
    by_cases hm'S : m' = S.card
    · have hconsec' : ∀ m'', 1 ≤ m'' → m'' ≤ S.card - 1 →
          ∃ u ∈ BdFin umax, (BdFin u).card = m'' := by
        intro m'' hm1'' hmle''
        have hne2 : m'' ≠ m' := by omega
        exact hall' m'' hm1'' (by omega) hne2
      have hunion_eq : BdSuppSet (j + 2) c =
          BdSuppSet (j + 1) (BdFin umax) := by
        rw [hunion]
        rfl
      have ihC := ih (BdFin umax) humax_valid hucard hconsec'
      constructor
      · intro hun
        have hZ := ihC.1 (hunion_eq.symm.trans hun)
        have hcard := Finset.card_image_of_injOn hinjZ
        exact (congrArg Finset.card hVeq).trans (hcard.trans hZ)
      · intro hun
        have hZ := ihC.2 (fun h => hun (hunion_eq.trans h))
        have hcard := Finset.card_image_of_injOn hinjZ
        exact (congrArg Finset.card hVeq).trans (hcard.trans hZ)
    · have hm'lt : m' ≤ S.card - 1 := by omega
      have hZ2 : (Finset.univ.filter (fun z : BdV (n := n) (j + 1) =>
            z ∉ BdFin umax ∧ BdValid S (j + 1) {z} ∧
              ∀ w ∈ BdFin umax,
                BdFin z ⊆ BdFin w ∨ BdFin w ⊆ BdFin z)).card = 2 := by
        by_cases hm'1 : m' = 1
        · subst m'
          exact slot_below_two humax_valid hucard hS hm1' hm2' hmiss' hall'
            rfl
        · have hm'ge : 2 ≤ m' := by omega
          exact slot_between_two humax_valid hucard hS hm1' hm2' hmiss'
            hall' hm'ge hm'lt
      have hfull : BdSuppSet (j + 2) c = S := by
        obtain ⟨wstar, hwstar, hstarcard⟩ :=
          hall' S.card (by omega) le_rfl (by omega)
        rw [hunion]
        have humax_union : BdSuppSet (j + 1) (BdFin umax) =
            BdSupp (j + 1) wstar := by
          apply Finset.Subset.antisymm
          · intro j hj
            rw [mem_BdSuppSet] at hj
            obtain ⟨v, hvc, hjv⟩ := hj
            have hsub : BdFin v ⊆ BdFin wstar := by
              obtain ⟨uchain, umem, une⟩ := humax_valid
              have hbd : 1 ≤ (BdFin v).card ∧ (BdFin v).card ≤ S.card :=
                card_of_valid (umem v hvc)
              have hcomp := uchain v (Finset.mem_coe.mpr hvc) wstar
                (Finset.mem_coe.mpr hwstar)
              cases hcomp with
              | inl h => exact h
              | inr h =>
                have hle := Finset.card_le_card h
                rw [hstarcard] at hle
                have heq : BdFin wstar = BdFin v :=
                  Finset.eq_of_subset_of_card_le h (by omega)
                rw [heq]
            exact BdSupp_mono_succ hsub hjv
          · intro j hj
            rw [mem_BdSuppSet]
            exact ⟨wstar, hwstar, hj⟩
        have hsupp : BdSupp (j + 1) wstar = S := by
          have hvalid : BdValid S j (BdFin wstar) := by
            obtain ⟨uchain, umem, une⟩ := humax_valid
            exact umem wstar hwstar
          have hIH := supp_full_of_card_full hvalid hstarcard
          change (BdFin wstar).biUnion (BdSupp j) = S
          exact hIH
        change BdSuppSet (j + 1) (BdFin umax) = S
        rw [humax_union]
        exact hsupp
      constructor
      · intro _
        have hcard := Finset.card_image_of_injOn hinjZ
        exact (congrArg Finset.card hVeq).trans (hcard.trans hZ2)
      · intro hun
        exact absurd hfull hun

/-- Validity is monotone in the coordinate set. -/
private lemma valid_mono_S {S S' : Finset (Fin (n + 1))} (hSS : S' ⊆ S) :
    ∀ {k} {σ : Finset (BdV (n := n) k)}, BdValid S' k σ → BdValid S k σ := by
  intro k
  induction k with
  | zero =>
    intro σ h
    exact ⟨h.1.trans hSS, h.2⟩
  | succ k ih =>
    intro σ h
    obtain ⟨hchain, hmem, hne⟩ := h
    exact ⟨hchain, fun v hv => ih (hmem v hv), hne⟩

/-- A valid set supported inside a face is valid over that face. -/
private lemma valid_of_supp_subset {S S' : Finset (Fin (n + 1))} :
    ∀ {k} {σ : Finset (BdV (n := n) k)},
      BdValid S k σ → BdSuppSet k σ ⊆ S' → BdValid S' k σ := by
  intro k
  induction k with
  | zero =>
    intro σ h hsupp
    refine ⟨?_, h.2⟩
    intro y hy
    have hmem : y ∈ BdSuppSet 0 σ :=
      mem_BdSuppSet.mpr ⟨y, hy, Finset.mem_singleton_self y⟩
    exact hsupp hmem
  | succ k ih =>
    intro σ h hsupp
    obtain ⟨hchain, hmem, hne⟩ := h
    refine ⟨hchain, ?_, hne⟩
    intro v hv
    apply ih (hmem v hv)
    intro j hj
    have hj2 : j ∈ BdSuppSet (k + 1) σ := by
      rw [mem_BdSuppSet]
      exact ⟨v, hv, hj⟩
    exact hsupp hj2

/-- Erasing a vertex from a valid set of card ≥ 2 stays valid. -/
private lemma valid_erase {S : Finset (Fin (n + 1))} {k : ℕ}
    {T : Finset (BdV (n := n) k)} {v : BdV (n := n) k}
    (hT : BdValid S k T) (hv : v ∈ T) (hcard : 2 ≤ T.card) :
    BdValid S k (T.erase v) := by
  apply valid_subset_of_valid hT (Finset.erase_subset v T)
  have hpos : 0 < (T.erase v).card := by
    rw [Finset.card_erase_of_mem hv]
    omega
  exact Finset.card_pos.mp hpos

/-- Valid sets over a singleton coordinate set are singletons. -/
private lemma card_one_of_valid_singleton {S : Finset (Fin (n + 1))}
    (hS : S.card = 1) : ∀ {k} {σ : Finset (BdV (n := n) k)},
      BdValid S k σ → σ.card = 1 := by
  intro k
  induction k with
  | zero =>
    intro σ h
    have hcard := Finset.card_le_card h.1
    have hpos : 0 < σ.card := Finset.card_pos.mpr h.2
    have hle : σ.card ≤ 1 := hcard.trans hS.le
    exact Nat.le_antisymm hle hpos
  | succ k ih =>
    intro σ h
    obtain ⟨hchain, hmem, hne⟩ := h
    have hmem1 : ∀ v ∈ σ, (BdFin v).card = 1 := fun v hv => ih (hmem v hv)
    have halleq : ∀ a ∈ σ, ∀ b ∈ σ, BdFin a = BdFin b := by
      intro a ha b hb
      have hcomp := hchain a (Finset.mem_coe.mpr ha) b (Finset.mem_coe.mpr hb)
      have ha1 := hmem1 a ha
      have hb1 := hmem1 b hb
      cases hcomp with
      | inl h => exact Finset.eq_of_subset_of_card_le h (by omega)
      | inr h => exact (Finset.eq_of_subset_of_card_le h (by omega)).symm
    have hsub1 : σ.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      exact halleq a ha b hb
    have hpos : 0 < σ.card := Finset.card_pos.mpr hne
    omega

/-- Over a singleton coordinate set there is a unique valid vertex. -/
private lemma unique_vertex_singleton {S : Finset (Fin (n + 1))}
    (hS : S.card = 1) (k : ℕ) : ∃! v : BdV (n := n) k, BdValid S k {v} := by
  induction k with
  | zero =>
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hS
    refine ⟨i, ?_, ?_⟩
    · refine ⟨?_, Finset.singleton_nonempty i⟩
      intro y hy
      have hy2 : y = i := Finset.mem_singleton.mp hy
      subst y
      rw [hi]
      exact Finset.mem_singleton_self i
    · intro v hv
      have hsub : ({v} : Finset (BdV (n := n) 0)) ⊆ S := hv.1
      have hmem : v ∈ S := hsub (Finset.mem_singleton_self v)
      rw [hi] at hmem
      exact Finset.mem_singleton.mp hmem
  | succ k ih =>
    obtain ⟨u, hu, huniq⟩ := ih
    refine ⟨({u} : Finset (BdV (n := n) k)), ?_, ?_⟩
    · refine ⟨?_, ?_, Finset.singleton_nonempty _⟩
      · intro a ha b hb
        rw [Finset.mem_coe] at ha hb
        have ha2 := Finset.mem_singleton.mp ha
        have hb2 := Finset.mem_singleton.mp hb
        subst a
        subst b
        exact Or.inl (Finset.Subset.refl _)
      · intro w hw
        have hw2 := Finset.mem_singleton.mp hw
        subst w
        exact hu
    · intro v hv
      obtain ⟨hchain, hmem, hne⟩ := hv
      have hBv : BdValid S k (BdFin v) := hmem v (Finset.mem_singleton_self v)
      have hcard1 : (BdFin v).card = 1 := card_one_of_valid_singleton hS hBv
      obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard1
      have hwv : w ∈ BdFin v := by
        rw [hw]
        exact Finset.mem_singleton_self w
      have hwu : BdValid S k {w} := valid_singleton_of_mem hBv hwv
      have hwu_eq : w = u := huniq w hwu
      change BdFin v = {u}
      rw [hw, hwu_eq]

/-- The support of a valid set lies inside the coordinate set. -/
private lemma BdSuppSet_subset_of_valid {S : Finset (Fin (n + 1))} {k : ℕ}
    {σ : Finset (BdV (n := n) k)} (hσ : BdValid S k σ) :
    BdSuppSet k σ ⊆ S := by
  intro j hj
  rw [mem_BdSuppSet] at hj
  obtain ⟨v, hv, hjv⟩ := hj
  have hvs : BdValid S k {v} := valid_singleton_of_mem hσ hv
  exact BdSupp_subset hvs hjv

open Classical in
/-- Door-count parity summed over tops equals the fully-labeled count mod 2. -/
private lemma doors_parity_sum {S : Finset (Fin (n + 1))} {k : ℕ}
    {l : BdV (n := n) (k + 1) → Fin (n + 1)}
    (hSper : ∀ v, BdValid S (k + 1) {v} → l v ∈ BdSupp (k + 1) v)
    {c : Fin (n + 1)} (hc : c ∈ S) :
    (∑ T ∈ Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card),
      (T.filter (fun v => (T.erase v).image l = S.erase c)).card) % 2 =
    (Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card ∧ T.image l = S)).card % 2 := by
  have hterm : ∀ T ∈ Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
      BdValid S (k + 1) T ∧ T.card = S.card),
      (T.filter (fun v => (T.erase v).image l = S.erase c)).card % 2 =
        (if T.image l = S then 1 else 0) := by
    intro T hT
    rw [Finset.mem_filter] at hT
    obtain ⟨hmem, hTvalid, hTcard⟩ := hT
    have hmaps : ∀ v ∈ T, l v ∈ S := by
      intro v hv
      have hvv : BdValid S (k + 1) {v} := valid_singleton_of_mem hTvalid hv
      exact BdSupp_subset hvv (hSper v hvv)
    exact single_parity T S c hc l hmaps hTcard
  have hsum : (∑ T ∈ Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
      BdValid S (k + 1) T ∧ T.card = S.card),
      (if T.image l = S then 1 else 0)) =
      (Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card ∧ T.image l = S)).card := by
    have hfil : ((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card)).filter
        (fun T => T.image l = S)).card =
        (Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
          BdValid S (k + 1) T ∧ T.card = S.card ∧ T.image l = S)).card := by
      congr 1
      ext T
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        obtain ⟨⟨hvalid, hcard⟩, him⟩ := h
        exact ⟨hvalid, hcard, him⟩
      · intro h
        obtain ⟨hvalid, hcard, him⟩ := h
        exact ⟨⟨hvalid, hcard⟩, him⟩
    have hcard1 : (((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card)).filter
        (fun T => T.image l = S))).card =
        ∑ T ∈ Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
          BdValid S (k + 1) T ∧ T.card = S.card),
          (if T.image l = S then 1 else 0) := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact hcard1.symm.trans hfil
  calc (∑ T ∈ Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card),
      (T.filter (fun v => (T.erase v).image l = S.erase c)).card) % 2
      = (∑ T ∈ Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
          BdValid S (k + 1) T ∧ T.card = S.card),
          (T.filter (fun v => (T.erase v).image l = S.erase c)).card % 2) % 2 :=
        Finset.sum_nat_mod _ _ _
    _ = (∑ T ∈ Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
          BdValid S (k + 1) T ∧ T.card = S.card),
          (if T.image l = S then 1 else 0)) % 2 := by
        have hcongr : (∑ T ∈ Finset.univ.filter
            (fun T : Finset (BdV (n := n) (k + 1)) =>
              BdValid S (k + 1) T ∧ T.card = S.card),
            (T.filter (fun v => (T.erase v).image l = S.erase c)).card % 2) =
            (∑ T ∈ Finset.univ.filter
              (fun T : Finset (BdV (n := n) (k + 1)) =>
                BdValid S (k + 1) T ∧ T.card = S.card),
              (if T.image l = S then 1 else 0)) :=
          Finset.sum_congr rfl (fun T hT => hterm T hT)
        rw [hcongr]
    _ = (Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
          BdValid S (k + 1) T ∧ T.card = S.card ∧ T.image l = S)).card % 2 := by
        rw [hsum]

open Classical in
/-- Pairs count as door-counts summed over tops. -/
private lemma pairs_eq_sum_doors {S : Finset (Fin (n + 1))} {k : ℕ}
    {l : BdV (n := n) (k + 1) → Fin (n + 1)} {c : Fin (n + 1)} :
    ((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card)).sigma
      (fun T => T.filter (fun v => (T.erase v).image l = S.erase c))).card =
    ∑ T ∈ Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card),
      (T.filter (fun v => (T.erase v).image l = S.erase c)).card :=
  Finset.card_sigma _ _

open Classical in
/-- Pairs count as fibers summed over doors. -/
private lemma pairs_eq_sum_fiber {S : Finset (Fin (n + 1))} {k : ℕ}
    {l : BdV (n := n) (k + 1) → Fin (n + 1)} {c : Fin (n + 1)}
    (hS2 : 2 ≤ S.card) :
    ((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card)).sigma
      (fun T => T.filter (fun v => (T.erase v).image l = S.erase c))).card =
    ∑ D ∈ Finset.univ.filter (fun D : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) D ∧ D.card = S.card - 1 ∧ D.image l = S.erase c),
      (((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card)).sigma
        (fun T => T.filter (fun v => (T.erase v).image l = S.erase c))).filter
        (fun p => p.1.erase p.2 = D)).card := by
  apply Finset.card_eq_sum_card_fiberwise (f := fun p : Sigma
    (fun _ : Finset (BdV (n := n) (k + 1)) => BdV (n := n) (k + 1)) =>
      p.1.erase p.2)
  intro p hp
  rw [Finset.mem_coe, Finset.mem_sigma] at hp
  obtain ⟨hTops, hv⟩ := hp
  rw [Finset.mem_filter] at hTops hv
  rw [Finset.mem_coe, Finset.mem_filter] at ⊢
  obtain ⟨hmemT, hTvalid, hTcard⟩ := hTops
  obtain ⟨hvT, hvim⟩ := hv
  refine ⟨Finset.mem_univ _, ?_, ?_, hvim⟩
  · exact valid_erase hTvalid hvT (by omega)
  · have h1 : (p.1.erase p.2).card = S.card - 1 := by
      rw [Finset.card_erase_of_mem hvT, hTcard]
    exact h1

open Classical in
/-- Each door-fiber counts the tops containing that door. -/
private lemma fiber_eq_tops {S : Finset (Fin (n + 1))} {k : ℕ}
    {l : BdV (n := n) (k + 1) → Fin (n + 1)} {c : Fin (n + 1)}
    (hS2 : 2 ≤ S.card) (_hc : c ∈ S)
    (D : Finset (BdV (n := n) (k + 1)))
    (hD : D ∈ Finset.univ.filter (fun D : Finset (BdV (n := n) (k + 1)) =>
      BdValid S (k + 1) D ∧ D.card = S.card - 1 ∧ D.image l = S.erase c)) :
    (((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card)).sigma
      (fun T => T.filter (fun v => (T.erase v).image l = S.erase c))).filter
      (fun p => p.1.erase p.2 = D)).card =
    ((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card)).filter
      (fun T => D ⊆ T)).card := by
  rw [Finset.mem_filter] at hD
  obtain ⟨hmemD, hDvalid, hDcard, hDlabels⟩ := hD
  have himg : (((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
      BdValid S (k + 1) T ∧ T.card = S.card)).sigma
      (fun T => T.filter (fun v => (T.erase v).image l = S.erase c))).filter
      (fun p => p.1.erase p.2 = D)).image Sigma.fst =
      (Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card)).filter
      (fun T => D ⊆ T) := by
    ext T
    constructor
    · intro h
      rw [Finset.mem_image] at h
      obtain ⟨p, hpfil, rfl⟩ := h
      rw [Finset.mem_filter] at hpfil ⊢
      obtain ⟨hpP, hperase⟩ := hpfil
      rw [Finset.mem_sigma] at hpP
      obtain ⟨hpTops, hpv⟩ := hpP
      refine ⟨hpTops, ?_⟩
      have hsub : D ⊆ p.1 := by
        rw [← hperase]
        exact Finset.erase_subset _ _
      exact hsub
    · intro h
      rw [Finset.mem_filter] at h
      obtain ⟨hTops, hsub⟩ := h
      rw [Finset.mem_filter] at hTops
      obtain ⟨hmemT, hTvalid, hTcard⟩ := hTops
      have hTopsMem : T ∈ Finset.univ.filter
          (fun T : Finset (BdV (n := n) (k + 1)) =>
            BdValid S (k + 1) T ∧ T.card = S.card) :=
        Finset.mem_filter.mpr ⟨hmemT, hTvalid, hTcard⟩
      have hne : D ≠ T := by
        intro hcon
        rw [hcon, hTcard] at hDcard
        omega
      have hss : D ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
      obtain ⟨v, hvT, hvD⟩ := Finset.exists_of_ssubset hss
      have herase : T.erase v = D := by
        apply Finset.Subset.antisymm
        · intro x hx
          rw [Finset.mem_erase] at hx
          obtain ⟨hxne, hxT⟩ := hx
          by_contra hxD
          have hsub2 : insert x (insert v D) ⊆ T := by
            intro y hy
            rw [Finset.mem_insert, Finset.mem_insert] at hy
            rcases hy with rfl | rfl | hyD
            · exact hxT
            · exact hvT
            · exact hsub hyD
          have hnotmem2 : x ∉ insert v D := by
            rw [Finset.mem_insert]
            intro hcon
            rcases hcon with rfl | hD2
            · exact hxne rfl
            · exact hxD hD2
          have hcard2 := Finset.card_le_card hsub2
          rw [Finset.card_insert_of_notMem hnotmem2,
            Finset.card_insert_of_notMem hvD] at hcard2
          omega
        · intro x hxD
          have hxne : x ≠ v := by
            intro hcon
            subst hcon
            exact hvD hxD
          exact Finset.mem_erase.mpr ⟨hxne, hsub hxD⟩
      have hdoor : v ∈ T.filter (fun v => (T.erase v).image l = S.erase c) := by
        rw [Finset.mem_filter]
        refine ⟨hvT, ?_⟩
        rw [herase]
        exact hDlabels
      have hPmem : (⟨T, v⟩ : Sigma (fun _ : Finset (BdV (n := n) (k + 1)) =>
          BdV (n := n) (k + 1))) ∈
          (Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
            BdValid S (k + 1) T ∧ T.card = S.card)).sigma
          (fun T => T.filter (fun v => (T.erase v).image l = S.erase c)) := by
        rw [Finset.mem_sigma]
        exact ⟨hTopsMem, hdoor⟩
      have hfilm : (⟨T, v⟩ : Sigma (fun _ : Finset (BdV (n := n) (k + 1)) =>
          BdV (n := n) (k + 1))) ∈
          (((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
            BdValid S (k + 1) T ∧ T.card = S.card)).sigma
            (fun T => T.filter (fun v => (T.erase v).image l = S.erase c))).filter
          (fun p => p.1.erase p.2 = D)) :=
        Finset.mem_filter.mpr ⟨hPmem, herase⟩
      exact Finset.mem_image.mpr ⟨⟨T, v⟩, hfilm, rfl⟩
  have hinj : Set.InjOn Sigma.fst ((↑((((Finset.univ.filter
      (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card)).sigma
      (fun T => T.filter (fun v => (T.erase v).image l = S.erase c))).filter
      (fun p => p.1.erase p.2 = D))) :
      Set (Sigma fun _ : Finset (BdV (n := n) (k + 1)) => BdV (n := n) (k + 1)))) := by
    intro p hp q hq hfst
    rw [Finset.mem_coe, Finset.mem_filter] at hp hq
    obtain ⟨hpP, hperase⟩ := hp
    obtain ⟨hqP, hqerase⟩ := hq
    cases p with
    | mk T v =>
      cases q with
      | mk T' v' =>
        have hTT : T = T' := hfst
        rw [Finset.mem_sigma] at hpP hqP
        obtain ⟨-, hpv⟩ := hpP
        obtain ⟨-, hqv⟩ := hqP
        rw [Finset.mem_filter] at hpv hqv
        obtain ⟨hvT, -⟩ := hpv
        obtain ⟨hvT', -⟩ := hqv
        have hvv : v = v' := by
          by_contra hne
          have hvT'' : v ∈ T' := by rw [← hTT]; exact hvT
          have hmem1 : v ∈ T'.erase v' := Finset.mem_erase.mpr ⟨hne, hvT''⟩
          have hmem2 : v ∉ T.erase v := by
            rw [Finset.mem_erase]
            intro hcon
            exact hcon.1 rfl
          rw [hqerase] at hmem1
          rw [hperase] at hmem2
          exact hmem2 hmem1
        subst hTT
        exact congrArg (Sigma.mk _) hvv
  exact (Finset.card_image_of_injOn hinj).symm.trans
    (congrArg Finset.card himg)

open Classical in
/-- Tops over a door: even for interior doors, odd for boundary doors. -/
private lemma tops_containing_parity {S : Finset (Fin (n + 1))} {k : ℕ}
    (hS2 : 2 ≤ S.card)
    (D : Finset (BdV (n := n) (k + 1)))
    (hDvalid : BdValid S (k + 1) D) (hDcard : D.card = S.card - 1) :
    ((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card)).filter
      (fun T => D ⊆ T)).card % 2 =
      (if BdSuppSet (k + 1) D = S then 0 else 1) := by
  have hDcopy := hDvalid
  obtain ⟨hDchain, hDmem, hDne⟩ := hDvalid
  have himg : ((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card)).filter
      (fun T => D ⊆ T)) =
      (Finset.univ.filter (fun x : BdV (n := n) (k + 1) =>
        x ∉ D ∧ BdValid S (k + 1) {x} ∧
          ∀ w ∈ D, BdFin x ⊆ BdFin w ∨ BdFin w ⊆ BdFin x)).image
        (fun x => insert x D) := by
    ext T
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · intro h
      obtain ⟨hTtops, hsub⟩ := h
      rw [Finset.mem_filter] at hTtops
      obtain ⟨-, hTvalid, hTcard⟩ := hTtops
      have hne : D ≠ T := by
        intro hcon
        rw [hcon, hTcard] at hDcard
        omega
      have hss : D ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
      have hcard1 : T.card = D.card + 1 := by omega
      obtain ⟨x, hxD, rfl⟩ := insert_of_ssubset_card hss hcard1
      refine ⟨x, ?_, rfl⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, hxD, ?_, ?_⟩
      · exact valid_singleton_of_mem hTvalid (Finset.mem_insert_self x D)
      · intro w hw
        obtain ⟨hTchain, _, _⟩ := hTvalid
        exact hTchain x (Finset.mem_coe.mpr (Finset.mem_insert_self x D)) w
          (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hw))
    · intro h
      obtain ⟨x, hxfil, rfl⟩ := h
      rw [Finset.mem_filter] at hxfil
      obtain ⟨-, hxD, hxvalid, hxcomp⟩ := hxfil
      obtain ⟨hxchain, hxmem, _⟩ := hxvalid
      rw [Finset.mem_filter]
      refine ⟨?_, Finset.subset_insert x D⟩
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · refine ⟨?_, ?_, Finset.insert_nonempty x D⟩
        · intro a ha b hb
          rw [Finset.mem_coe, Finset.mem_insert] at ha hb
          cases ha with
          | inl hax =>
            cases hb with
            | inl hbx =>
              rw [hax, hbx]
              exact Or.inl (Finset.Subset.refl _)
            | inr hbD =>
              rw [hax]
              exact hxcomp b hbD
          | inr haD =>
            cases hb with
            | inl hbx =>
              rw [hbx]
              cases hxcomp a haD with
              | inl h => exact Or.inr h
              | inr h => exact Or.inl h
            | inr hbD =>
              exact hDchain a (Finset.mem_coe.mpr haD) b
                (Finset.mem_coe.mpr hbD)
        · intro v hv
          rw [Finset.mem_insert] at hv
          have hxmemx := hxmem x (Finset.mem_singleton_self x)
          cases hv with
          | inl h =>
            rw [h]
            exact hxmemx
          | inr h => exact hDmem v h
      · rw [Finset.card_insert_of_notMem hxD, hDcard]
        omega
  have hinj : Set.InjOn (fun x : BdV (n := n) (k + 1) => insert x D)
      ↑(Finset.univ.filter (fun x : BdV (n := n) (k + 1) =>
        x ∉ D ∧ BdValid S (k + 1) {x} ∧
          ∀ w ∈ D, BdFin x ⊆ BdFin w ∨ BdFin w ⊆ BdFin x)) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter] at hx hy
    obtain ⟨-, hxD, _, _⟩ := hx
    obtain ⟨-, hyD, _, _⟩ := hy
    have hxy2 : insert x D = insert y D := hxy
    have hxmem : x ∈ insert y D := by
      rw [← hxy2]
      exact Finset.mem_insert_self x D
    rw [Finset.mem_insert] at hxmem
    cases hxmem with
    | inl h => exact h
    | inr h => exact absurd h hxD
  have hcard : ((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
      BdValid S (k + 1) T ∧ T.card = S.card)).filter
      (fun T => D ⊆ T)).card =
      (Finset.univ.filter (fun x : BdV (n := n) (k + 1) =>
        x ∉ D ∧ BdValid S (k + 1) {x} ∧
          ∀ w ∈ D, BdFin x ⊆ BdFin w ∨ BdFin w ⊆ BdFin x)).card := by
    rw [himg, Finset.card_image_of_injOn hinj]
  obtain ⟨m, hm1, hm2, hmiss, hall⟩ := missing_card_exists hDcopy hDcard
  have hgap_supp : m ≠ S.card → BdSuppSet (k + 1) D = S := by
    intro hne
    have h1 : 1 ≤ S.card := by omega
    obtain ⟨u, hu, hucard⟩ := hall S.card h1 le_rfl (Ne.symm hne)
    have hBu : BdValid S k (BdFin u) := hDmem u hu
    have hsup : BdSuppSet k (BdFin u) = S := supp_full_of_card_full hBu hucard
    apply Finset.Subset.antisymm
    · exact BdSuppSet_subset_of_valid hDcopy
    · intro j hj
      rw [mem_BdSuppSet]
      refine ⟨u, hu, ?_⟩
      rw [mem_BdSupp_succ]
      have hj2 : j ∈ BdSuppSet k (BdFin u) := by
        rw [hsup]
        exact hj
      rw [mem_BdSuppSet] at hj2
      exact hj2
  have hconsec : m = S.card → ∀ m', 1 ≤ m' → m' ≤ S.card - 1 →
      ∃ u ∈ D, (BdFin u).card = m' := by
    intro hmeq m' hm1' hmle
    exact hall m' hm1' (by omega) (by omega)
  by_cases hmsup : BdSuppSet (k + 1) D = S
  · rw [ite_eq_left hmsup]
    have hE2 : (Finset.univ.filter (fun x : BdV (n := n) (k + 1) =>
        x ∉ D ∧ BdValid S (k + 1) {x} ∧
          ∀ w ∈ D, BdFin x ⊆ BdFin w ∨ BdFin w ⊆ BdFin x)).card = 2 := by
      by_cases hmeq : m = S.card
      · exact (consec_slot_count hS2 k D hDcopy hDcard
          (hconsec hmeq)).1 hmsup
      · have hmle : m ≤ S.card - 1 := by omega
        by_cases hm1eq : m = 1
        · exact slot_below_two hDcopy hDcard hS2 hm1 hm2 hmiss hall hm1eq
        · have hmlo : 2 ≤ m := by omega
          exact slot_between_two hDcopy hDcard hS2 hm1 hm2 hmiss hall hmlo hmle
    rw [hcard, hE2]
  · rw [ite_eq_right hmsup]
    have hmeq : m = S.card := by
      by_contra hne
      exact hmsup (hgap_supp hne)
    have hE1 : (Finset.univ.filter (fun x : BdV (n := n) (k + 1) =>
        x ∉ D ∧ BdValid S (k + 1) {x} ∧
          ∀ w ∈ D, BdFin x ⊆ BdFin w ∨ BdFin w ⊆ BdFin x)).card = 1 :=
      (consec_slot_count hS2 k D hDcopy hDcard (hconsec hmeq)).2 hmsup
    rw [hcard, hE1]

open Classical in
/-- Sperner parity step: full-simplex count mod 2 transfers to the face. -/
private lemma sperner_step {S : Finset (Fin (n + 1))} {k : ℕ}
    {l : BdV (n := n) (k + 1) → Fin (n + 1)}
    (hSper : ∀ v, BdValid S (k + 1) {v} → l v ∈ BdSupp (k + 1) v)
    (hS2 : 2 ≤ S.card) {c : Fin (n + 1)} (hc : c ∈ S) :
    (Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card ∧ T.image l = S)).card % 2 =
    (Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid (S.erase c) (k + 1) T ∧ T.card = (S.erase c).card ∧
          T.image l = S.erase c)).card % 2 := by
  have hdoor := doors_parity_sum hSper hc
  have hsigma := pairs_eq_sum_doors (S := S) (k := k) (l := l) (c := c)
  have hfiber := pairs_eq_sum_fiber (S := S) (k := k) (l := l) (c := c) hS2
  have h1 : (Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card ∧ T.image l = S)).card % 2 =
      (∑ T ∈ Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card),
        (T.filter (fun v => (T.erase v).image l = S.erase c)).card) % 2 :=
    hdoor.symm
  have h2 : (∑ T ∈ Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card),
        (T.filter (fun v => (T.erase v).image l = S.erase c)).card) % 2 =
      ((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card)).sigma
        (fun T => T.filter (fun v => (T.erase v).image l = S.erase c))).card % 2 := by
    rw [hsigma]
  have h3 : ((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card)).sigma
        (fun T => T.filter (fun v => (T.erase v).image l = S.erase c))).card % 2 =
      (∑ D ∈ Finset.univ.filter (fun D : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) D ∧ D.card = S.card - 1 ∧ D.image l = S.erase c),
        (((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
          BdValid S (k + 1) T ∧ T.card = S.card)).sigma
          (fun T => T.filter (fun v => (T.erase v).image l = S.erase c))).filter
          (fun p => p.1.erase p.2 = D)).card) % 2 := by
    rw [hfiber]
  have hsum2 : (∑ D ∈ Finset.univ.filter (fun D : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) D ∧ D.card = S.card - 1 ∧ D.image l = S.erase c),
        (((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
          BdValid S (k + 1) T ∧ T.card = S.card)).sigma
          (fun T => T.filter (fun v => (T.erase v).image l = S.erase c))).filter
          (fun p => p.1.erase p.2 = D)).card) % 2 =
      (∑ D ∈ Finset.univ.filter (fun D : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) D ∧ D.card = S.card - 1 ∧ D.image l = S.erase c),
        (if BdSuppSet (k + 1) D = S then 0 else 1)) % 2 := by
    have e1 : (∑ D ∈ Finset.univ.filter (fun D : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) D ∧ D.card = S.card - 1 ∧ D.image l = S.erase c),
        (((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
          BdValid S (k + 1) T ∧ T.card = S.card)).sigma
          (fun T => T.filter (fun v => (T.erase v).image l = S.erase c))).filter
          (fun p => p.1.erase p.2 = D)).card) % 2 =
        (∑ D ∈ Finset.univ.filter (fun D : Finset (BdV (n := n) (k + 1)) =>
          BdValid S (k + 1) D ∧ D.card = S.card - 1 ∧ D.image l = S.erase c),
          (((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
            BdValid S (k + 1) T ∧ T.card = S.card)).sigma
            (fun T => T.filter (fun v => (T.erase v).image l = S.erase c))).filter
            (fun p => p.1.erase p.2 = D)).card % 2) % 2 :=
      Finset.sum_nat_mod _ _ _
    have e2 : (∑ D ∈ Finset.univ.filter (fun D : Finset (BdV (n := n) (k + 1)) =>
          BdValid S (k + 1) D ∧ D.card = S.card - 1 ∧ D.image l = S.erase c),
          (((Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
            BdValid S (k + 1) T ∧ T.card = S.card)).sigma
            (fun T => T.filter (fun v => (T.erase v).image l = S.erase c))).filter
            (fun p => p.1.erase p.2 = D)).card % 2) =
        (∑ D ∈ Finset.univ.filter (fun D : Finset (BdV (n := n) (k + 1)) =>
          BdValid S (k + 1) D ∧ D.card = S.card - 1 ∧ D.image l = S.erase c),
          (if BdSuppSet (k + 1) D = S then 0 else 1)) := by
      apply Finset.sum_congr rfl
      intro D hD
      have hDmem := hD
      rw [Finset.mem_filter] at hD
      obtain ⟨-, hDvalid, hDcard, -⟩ := hD
      rw [fiber_eq_tops hS2 hc D hDmem]
      exact tops_containing_parity hS2 D hDvalid hDcard
    rw [e1, e2]
  have hif : ∀ D : Finset (BdV (n := n) (k + 1)),
      (if BdSuppSet (k + 1) D = S then 0 else 1) =
        (if BdSuppSet (k + 1) D ≠ S then 1 else 0) := by
    intro D
    by_cases h : BdSuppSet (k + 1) D = S <;> simp [h]
  have hsumif : (∑ D ∈ Finset.univ.filter (fun D : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) D ∧ D.card = S.card - 1 ∧ D.image l = S.erase c),
        (if BdSuppSet (k + 1) D = S then 0 else 1)) =
      (∑ D ∈ Finset.univ.filter (fun D : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) D ∧ D.card = S.card - 1 ∧ D.image l = S.erase c),
        (if BdSuppSet (k + 1) D ≠ S then 1 else 0)) :=
    Finset.sum_congr rfl (fun D _ => hif D)
  have hsum3 : (∑ D ∈ Finset.univ.filter (fun D : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) D ∧ D.card = S.card - 1 ∧ D.image l = S.erase c),
        (if BdSuppSet (k + 1) D ≠ S then 1 else 0)) =
      ((Finset.univ.filter (fun D : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) D ∧ D.card = S.card - 1 ∧ D.image l = S.erase c)).filter
        (fun D => BdSuppSet (k + 1) D ≠ S)).card := by
    conv_rhs => rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hface : ((Finset.univ.filter (fun D : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) D ∧ D.card = S.card - 1 ∧ D.image l = S.erase c)).filter
        (fun D => BdSuppSet (k + 1) D ≠ S)).card =
      (Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid (S.erase c) (k + 1) T ∧ T.card = (S.erase c).card ∧
          T.image l = S.erase c)).card := by
    congr 1
    ext D
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      obtain ⟨⟨hvalid, hcard, him⟩, hne⟩ := h
      have hsubS : BdSuppSet (k + 1) D ⊆ S := BdSuppSet_subset_of_valid hvalid
      have hsubE : S.erase c ⊆ BdSuppSet (k + 1) D := by
        intro j hj
        rw [mem_BdSuppSet]
        have hj2 : j ∈ D.image l := by
          rw [him]
          exact hj
        obtain ⟨v, hv, hvl⟩ := Finset.mem_image.mp hj2
        refine ⟨v, hv, ?_⟩
        rw [← hvl]
        exact hSper v (valid_singleton_of_mem hvalid hv)
      have hcardE : (S.erase c).card = S.card - 1 := Finset.card_erase_of_mem hc
      have hlt : (BdSuppSet (k + 1) D).card < S.card := by
        have hss : BdSuppSet (k + 1) D ⊂ S :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hsubS, hne⟩
        exact Finset.card_lt_card hss
      have hle : S.card - 1 ≤ (BdSuppSet (k + 1) D).card := by
        rw [← hcardE]
        exact Finset.card_le_card hsubE
      have hcardEq : (BdSuppSet (k + 1) D).card = (S.erase c).card := by omega
      have hsup : BdSuppSet (k + 1) D = S.erase c :=
        (Finset.eq_of_subset_of_card_le hsubE hcardEq.le).symm
      refine ⟨valid_of_supp_subset hvalid ?_, ?_, him⟩
      · rw [hsup]
      · rw [hcard, hcardE]
    · intro h
      obtain ⟨hvalid, hcard, him⟩ := h
      refine ⟨⟨?_, ?_, him⟩, ?_⟩
      · exact valid_mono_S (Finset.erase_subset c S) hvalid
      · rw [hcard, Finset.card_erase_of_mem hc]
      · intro hcon
        have hsub : BdSuppSet (k + 1) D ⊆ S.erase c :=
          BdSuppSet_subset_of_valid hvalid
        rw [hcon] at hsub
        have hmem := hsub hc
        rw [Finset.mem_erase] at hmem
        exact hmem.1 rfl
  rw [h1, h2, h3, hsum2, hsumif, hsum3, hface]

open Classical in
/-- Sperner base case: exactly one fully-labeled simplex over a singleton. -/
private lemma sperner_base {S : Finset (Fin (n + 1))} {k : ℕ}
    {l : BdV (n := n) (k + 1) → Fin (n + 1)}
    (hSper : ∀ v, BdValid S (k + 1) {v} → l v ∈ BdSupp (k + 1) v)
    (hS : S.card = 1) :
    Odd (Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
      BdValid S (k + 1) T ∧ T.card = S.card ∧ T.image l = S)).card := by
  obtain ⟨v₀, hv₀, huniq⟩ := unique_vertex_singleton hS (k + 1)
  have hfull : (Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
      BdValid S (k + 1) T ∧ T.card = S.card ∧ T.image l = S)) = {{v₀}} := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro h
      obtain ⟨hvalid, hcard, him⟩ := h
      rw [hS] at hcard
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
      have hvvalid : BdValid S (k + 1) {v} := by
        rw [← hv]
        exact hvalid
      have hveq : v = v₀ := huniq v hvvalid
      rw [hv, hveq]
    · intro h
      subst h
      refine ⟨hv₀, ?_, ?_⟩
      · rw [Finset.card_singleton, hS]
      · rw [Finset.image_singleton]
        apply Finset.eq_of_subset_of_card_le
        · intro j hj
          rw [Finset.mem_singleton] at hj
          rw [hj]
          exact BdSupp_subset hv₀ (hSper v₀ hv₀)
        · exact le_of_eq (by rw [hS, Finset.card_singleton])
  rw [hfull, Finset.card_singleton]
  exact odd_one

open Classical in
/-- Sperner lemma by induction on face size: full count is odd. -/
private lemma sperner_odd {k : ℕ}
    {l : BdV (n := n) (k + 1) → Fin (n + 1)} :
    ∀ (m : ℕ) (S : Finset (Fin (n + 1))), S.card = m + 1 →
      (∀ v, BdValid S (k + 1) {v} → l v ∈ BdSupp (k + 1) v) →
      Odd (Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
        BdValid S (k + 1) T ∧ T.card = S.card ∧ T.image l = S)).card := by
  intro m
  induction m with
  | zero =>
    intro S hS hSper
    exact sperner_base hSper hS
  | succ m ih =>
    intro S hS hSperS
    have hS2 : 2 ≤ S.card := by omega
    have hpos : 0 < S.card := by omega
    obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos
    have hcardE : (S.erase c).card = m + 1 := by
      rw [Finset.card_erase_of_mem hc, hS]
      omega
    have hSperE : ∀ v, BdValid (S.erase c) (k + 1) {v} →
        l v ∈ BdSupp (k + 1) v :=
      fun v hv => hSperS v (valid_mono_S (Finset.erase_subset c S) hv)
    have hstep := sperner_step hSperS hS2 hc
    have ihE := ih (S.erase c) hcardE hSperE
    rw [Nat.odd_iff] at ihE ⊢
    rw [hstep]
    exact ihE

open Classical in
/-- Sperner existence over the full simplex. -/
private lemma sperner_exists {k : ℕ}
    {l : BdV (n := n) (k + 1) → Fin (n + 1)}
    (hSper : ∀ v, BdValid Finset.univ (k + 1) {v} → l v ∈ BdSupp (k + 1) v) :
    ∃ T : Finset (BdV (n := n) (k + 1)),
      BdValid Finset.univ (k + 1) T ∧
        T.card = (Finset.univ : Finset (Fin (n + 1))).card ∧
        T.image l = Finset.univ := by
  have h := sperner_odd n Finset.univ
    (by rw [Finset.card_univ, Fintype.card_fin]) hSper
  obtain ⟨r, hr⟩ := h
  have hpos : 0 < (Finset.univ.filter (fun T : Finset (BdV (n := n) (k + 1)) =>
      BdValid Finset.univ (k + 1) T ∧
        T.card = (Finset.univ : Finset (Fin (n + 1))).card ∧
        T.image l = Finset.univ)).card := by omega
  obtain ⟨T, hT⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hT
  obtain ⟨-, hvalid, hcard, him⟩ := hT
  exact ⟨T, hvalid, hcard, him⟩

/-- Difference of averages is bounded by the max pairwise difference. -/
private lemma abs_avg_sub_avg_le {ι : Type*} {A B : Finset ι}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (f : ι → ℝ) (D : ℝ)
    (hD : ∀ a ∈ A, ∀ b ∈ B, |f a - f b| ≤ D) :
    |(∑ a ∈ A, f a) / (A.card : ℝ) - (∑ b ∈ B, f b) / (B.card : ℝ)| ≤ D := by
  have hp : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have hq : 0 < (B.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hB
  have hp' : (A.card : ℝ) ≠ 0 := ne_of_gt hp
  have hq' : (B.card : ℝ) ≠ 0 := ne_of_gt hq
  have hinner : ∀ a ∈ A, (∑ b ∈ B, (f a - f b)) =
      (B.card : ℝ) * f a - (∑ b ∈ B, f b) := by
    intro a ha
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hexpand : (∑ a ∈ A, ∑ b ∈ B, (f a - f b)) =
      (B.card : ℝ) * (∑ a ∈ A, f a) - (A.card : ℝ) * (∑ b ∈ B, f b) := by
    have hcongr : (∑ a ∈ A, ∑ b ∈ B, (f a - f b)) =
        ∑ a ∈ A, ((B.card : ℝ) * f a - (∑ b ∈ B, f b)) :=
      Finset.sum_congr rfl (fun a ha => hinner a ha)
    rw [hcongr, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
  have hdiv : (∑ a ∈ A, f a) / (A.card : ℝ) - (∑ b ∈ B, f b) / (B.card : ℝ) =
      (∑ a ∈ A, ∑ b ∈ B, (f a - f b)) / ((A.card : ℝ) * B.card) := by
    rw [hexpand, div_sub_div _ _ hp' hq']
    congr 1
    ring
  rw [hdiv, abs_div, abs_of_pos (mul_pos hp hq)]
  have hnum : |(∑ a ∈ A, ∑ b ∈ B, (f a - f b))| ≤
      (A.card : ℝ) * B.card * D := by
    calc |(∑ a ∈ A, ∑ b ∈ B, (f a - f b))|
        ≤ ∑ a ∈ A, ∑ b ∈ B, |f a - f b| := by
          calc |∑ a ∈ A, ∑ b ∈ B, (f a - f b)|
              ≤ ∑ a ∈ A, |∑ b ∈ B, (f a - f b)| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ a ∈ A, ∑ b ∈ B, |f a - f b| :=
              Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ a ∈ A, ∑ b ∈ B, D :=
        Finset.sum_le_sum (fun a ha =>
          Finset.sum_le_sum (fun b hb => hD a ha b hb))
      _ = (A.card : ℝ) * B.card * D := by
          rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
          ring
  rw [div_le_iff₀ (mul_pos hp hq)]
  rw [mul_comm D _]
  exact hnum

/-- Averaging over a nested pair contracts by the missing fraction. -/
private lemma abs_avg_nested_le {ι : Type*} {A B : Finset ι}
    (hAB : A ⊆ B) (hA : A.Nonempty)
    (f : ι → ℝ) (D : ℝ)
    (hD : ∀ a ∈ A, ∀ b ∈ B, |f a - f b| ≤ D) :
    |(∑ b ∈ B, f b) / (B.card : ℝ) - (∑ a ∈ A, f a) / (A.card : ℝ)| ≤
      (((B.card : ℝ) - A.card) / B.card) * D := by
  classical
  have hp : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have hle : A.card ≤ B.card := Finset.card_le_card hAB
  have hq : 0 < (B.card : ℝ) := by
    have hpos : 0 < B.card := lt_of_lt_of_le (Finset.card_pos.mpr hA) hle
    exact_mod_cast hpos
  by_cases heq : A = B
  · subst heq
    simp
  · have hss : A ⊂ B := Finset.ssubset_iff_subset_ne.mpr ⟨hAB, heq⟩
    have hlt : A.card < B.card := Finset.card_lt_card hss
    have hCcard : (B \ A).card = B.card - A.card :=
      Finset.card_sdiff_of_subset hAB
    have hC : (B \ A).Nonempty :=
      Finset.card_pos.mp (by omega)
    have hr : 0 < ((B \ A).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hC
    have hp' : (A.card : ℝ) ≠ 0 := ne_of_gt hp
    have hq' : (B.card : ℝ) ≠ 0 := ne_of_gt hq
    have hr' : ((B \ A).card : ℝ) ≠ 0 := ne_of_gt hr
    have hrr : ((B \ A).card : ℝ) = (B.card : ℝ) - A.card := by
      rw [hCcard]
      exact Nat.cast_sub hle
    have hqp : (B.card : ℝ) - A.card ≠ 0 := by
      rw [← hrr]
      exact hr'
    have hunion : B \ A ∪ A = B := Finset.sdiff_union_of_subset hAB
    have hdecomp : (∑ b ∈ B, f b) =
        (∑ c ∈ B \ A, f c) + (∑ a ∈ A, f a) := by
      conv_lhs => rw [← hunion]
      exact Finset.sum_union Finset.disjoint_sdiff.symm
    have hfactor : (∑ b ∈ B, f b) / (B.card : ℝ) -
          (∑ a ∈ A, f a) / (A.card : ℝ) =
        (((B.card : ℝ) - A.card) / B.card) *
          ((∑ c ∈ B \ A, f c) / ((B \ A).card : ℝ) -
            (∑ a ∈ A, f a) / (A.card : ℝ)) := by
      rw [hdecomp, hrr]
      field_simp
      ring
    have hY : |(∑ c ∈ B \ A, f c) / ((B \ A).card : ℝ) -
        (∑ a ∈ A, f a) / (A.card : ℝ)| ≤ D :=
      abs_avg_sub_avg_le hC hA f D (fun c hc a ha => by
        rw [abs_sub_comm]
        exact hD a ha c (Finset.mem_sdiff.mp hc).1)
    have hXnn : 0 ≤ ((B.card : ℝ) - A.card) / B.card := by
      apply div_nonneg _ hq.le
      have hleR : (A.card : ℝ) ≤ B.card := by exact_mod_cast hle
      linarith
    rw [hfactor, abs_mul, abs_of_nonneg hXnn]
    exact mul_le_mul_of_nonneg_left hY hXnn

/-- Barycentric subdivision mesh shrinks geometrically. -/
private lemma mesh_le : ∀ {K : ℕ} {T : Finset (BdV (n := n) K)},
    BdValid Finset.univ K T → ∀ {v w : BdV (n := n) K},
    v ∈ T → w ∈ T → ∀ j : Fin (n + 1),
    |BdPt K v j - BdPt K w j| ≤ ((n : ℝ) / (n + 1)) ^ K := by
  intro K
  induction K with
  | zero =>
    intro T hT v w hv hw j
    change |(if j = BdFin0 v then (1 : ℝ) else 0) -
      (if j = BdFin0 w then (1 : ℝ) else 0)| ≤ ((n : ℝ) / (n + 1)) ^ 0
    rw [pow_zero]
    have h01 : ∀ (x y : ℝ), (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) →
        |x - y| ≤ 1 := by
      intro x y hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num
    refine h01 _ _ ?_ ?_ <;> split_ifs <;> simp
  | succ K ih =>
    intro T hT v w hv hw j
    have hmain : ∀ {A B : Finset (BdV (n := n) K)}, A ⊆ B → A.Nonempty →
        BdValid Finset.univ K B →
        |(∑ b ∈ B, BdPt K b j) / (B.card : ℝ) -
          (∑ a ∈ A, BdPt K a j) / (A.card : ℝ)| ≤
          ((n : ℝ) / (n + 1)) ^ (K + 1) := by
      intro A B hAB hAne hBvalid
      have hD : ∀ a ∈ A, ∀ b ∈ B,
          |BdPt K a j - BdPt K b j| ≤ ((n : ℝ) / (n + 1)) ^ K :=
        fun a ha b hb => ih hBvalid (hAB ha) hb j
      have hnest := abs_avg_nested_le hAB hAne (fun u => BdPt K u j)
        (((n : ℝ) / (n + 1)) ^ K) hD
      have hA1 : 1 ≤ A.card := Finset.card_pos.mpr hAne
      have hBle : B.card ≤ n + 1 := by
        have h2 := (card_of_valid hBvalid).2
        rw [Finset.card_univ, Fintype.card_fin] at h2
        exact h2
      have hBpos : (0 : ℝ) < B.card := by
        have hpos : 0 < B.card :=
          lt_of_lt_of_le (Finset.card_pos.mpr hAne) (Finset.card_le_card hAB)
        exact_mod_cast hpos
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hfactor : (((B.card : ℝ) - A.card) / B.card) ≤
          (n : ℝ) / (n + 1) := by
        rw [div_le_div_iff₀ hBpos hn1]
        have hcross : (B.card : ℝ) ≤ (A.card : ℝ) * ((n : ℝ) + 1) := by
          calc (B.card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hBle
            _ = 1 * ((n : ℝ) + 1) := (one_mul _).symm
            _ ≤ (A.card : ℝ) * ((n : ℝ) + 1) :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hA1) hn1.le
        have h1 : ((B.card : ℝ) - A.card) * ((n : ℝ) + 1) =
            (B.card : ℝ) * ((n : ℝ) + 1) - (A.card : ℝ) * ((n : ℝ) + 1) := by
          ring
        have h2 : (B.card : ℝ) * ((n : ℝ) + 1) =
            (n : ℝ) * B.card + B.card := by
          ring
        rw [h1, h2]
        linarith [hcross]
      have hDnn : 0 ≤ ((n : ℝ) / (n + 1)) ^ K := by positivity
      calc |(∑ b ∈ B, BdPt K b j) / (B.card : ℝ) -
            (∑ a ∈ A, BdPt K a j) / (A.card : ℝ)|
          ≤ (((B.card : ℝ) - A.card) / B.card) *
            (((n : ℝ) / (n + 1)) ^ K) := hnest
        _ ≤ ((n : ℝ) / (n + 1)) * (((n : ℝ) / (n + 1)) ^ K) :=
          mul_le_mul_of_nonneg_right hfactor hDnn
        _ = ((n : ℝ) / (n + 1)) ^ (K + 1) := by rw [pow_succ']
    obtain ⟨hchain, hmem, hne⟩ := hT
    have hcomp := hchain v (Finset.mem_coe.mpr hv) w (Finset.mem_coe.mpr hw)
    cases hcomp with
    | inl hsub =>
      change |(∑ u ∈ BdFin v, BdPt K u j) / ((BdFin v).card : ℝ) -
        (∑ u ∈ BdFin w, BdPt K u j) / ((BdFin w).card : ℝ)| ≤
        ((n : ℝ) / (n + 1)) ^ (K + 1)
      rw [abs_sub_comm]
      exact hmain hsub (nonempty_of_valid (hmem v hv)) (hmem w hw)
    | inr hsub =>
      change |(∑ u ∈ BdFin v, BdPt K u j) / ((BdFin v).card : ℝ) -
        (∑ u ∈ BdFin w, BdPt K u j) / ((BdFin w).card : ℝ)| ≤
        ((n : ℝ) / (n + 1)) ^ (K + 1)
      exact hmain hsub (nonempty_of_valid (hmem w hw)) (hmem v hv)

open Classical Topology Filter in
/-- **Knaster–Kuratowski–Mazurkiewicz lemma.** Let `F₀, …, Fₙ` be closed subsets of the
standard simplex `Δⁿ = Convexity.StdSimplex ℝ (Fin (n + 1))` such that every point `x` lies in
some `Fᵢ` with `xᵢ > 0`. Then the sets `Fᵢ` have a common point.

The covering hypothesis is the KKM condition in pointwise form: a point `x` lies in the face
spanned by the vertices of its support, so "every face `conv {eᵢ : i ∈ I}` is covered by
`⋃_{i ∈ I} Fᵢ`" is equivalent to it. The proof applies Sperner's lemma to the labelling
`x ↦ i` on the vertices of the `k`-th iterated barycentric subdivision, obtains a fully labelled
cell at every level, and passes to the limit using compactness, the mesh bound `(n/(n+1))ᵏ` and
closedness of the `Fᵢ`.

Source: B. Knaster, C. Kuratowski, S. Mazurkiewicz, "Ein Beweis des Fixpunktsatzes für
n-dimensionale Simplexe", Fundamenta Mathematicae 14 (1929), 132–137. -/
theorem kkm_lemma
    (F : Fin (n + 1) → Set (Convexity.StdSimplex ℝ (Fin (n + 1))))
    (hF_closed : ∀ i, IsClosed (F i))
    (hF_cover : ∀ x : Convexity.StdSimplex ℝ (Fin (n + 1)),
      ∃ i : Fin (n + 1), 0 < x.weights i ∧ x ∈ F i) :
    ∃ x : Convexity.StdSimplex ℝ (Fin (n + 1)), ∀ i, x ∈ F i := by
  have hSper : ∀ k : ℕ, ∀ v : BdV (n := n) (k + 1),
      BdValid Finset.univ (k + 1) {v} →
        BdLabel F hF_cover Finset.univ v ∈ BdSupp (k + 1) v :=
    fun k v hv => BdLabel_mem_supp hv
  have hex : ∀ k : ℕ, ∃ T : Finset (BdV (n := n) (k + 1)),
      BdValid Finset.univ (k + 1) T ∧
        T.card = (Finset.univ : Finset (Fin (n + 1))).card ∧
        T.image (BdLabel F hF_cover Finset.univ) = Finset.univ :=
    fun k => sperner_exists (l := BdLabel F hF_cover Finset.univ) (hSper k)
  choose Tk hTk using hex
  have hV : ∀ k : ℕ, ∃ V : Fin (n + 1) → BdV (n := n) (k + 1),
      ∀ i, V i ∈ Tk k ∧ BdLabel F hF_cover Finset.univ (V i) = i := by
    intro k
    have him := (hTk k).2.2
    have hexV : ∀ i : Fin (n + 1),
        ∃ v, v ∈ Tk k ∧ BdLabel F hF_cover Finset.univ v = i := by
      intro i
      have hi : i ∈ (Tk k).image (BdLabel F hF_cover Finset.univ) := by
        rw [him]
        exact Finset.mem_univ i
      obtain ⟨v, hv, hvl⟩ := Finset.mem_image.mp hi
      exact ⟨v, hv, hvl⟩
    choose V hV using hexV
    exact ⟨V, hV⟩
  choose V hV using hV
  have hVvalid : ∀ k i, BdValid Finset.univ (k + 1) {V k i} :=
    fun k i => valid_singleton_of_mem (hTk k).1 (hV k i).1
  set X : ℕ → (Fin (n + 1) → Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    fun k i => BdSimp (hVvalid k i) with hX
  haveI : T2Space (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).t2Space
  haveI : FirstCountableTopology (Convexity.StdSimplex ℝ (Fin (n + 1))) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ
      (Fin (n + 1))).firstCountableTopology
  obtain ⟨A, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq X
  have hcoord : ∀ i : Fin (n + 1),
      Tendsto (fun m => X (φ m) i) atTop (𝓝 (A i)) := by
    intro i
    have h := tendsto_pi_nhds.mp hlim i
    simpa [Function.comp_apply] using h
  have hbase0 : 0 ≤ (n : ℝ) / (n + 1) := by positivity
  have hbase1 : (n : ℝ) / (n + 1) < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    exact lt_add_one _
  have hpow0 : Tendsto (fun m : ℕ => ((n : ℝ) / (n + 1)) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1
  have hmesh : ∀ (i i' : Fin (n + 1)) (j : Fin (n + 1)) (m : ℕ),
      |BdPt (φ m + 1) (V (φ m) i) j - BdPt (φ m + 1) (V (φ m) i') j| ≤
        ((n : ℝ) / (n + 1)) ^ m := by
    intro i i' j m
    have h1 := mesh_le (hTk (φ m)).1 (hV (φ m) i).1 (hV (φ m) i').1 j
    have hle : m ≤ φ m + 1 := by
      have h2 : m ≤ φ m := hφ.le_apply
      omega
    calc |BdPt (φ m + 1) (V (φ m) i) j - BdPt (φ m + 1) (V (φ m) i') j|
        ≤ ((n : ℝ) / (n + 1)) ^ (φ m + 1) := h1
      _ ≤ ((n : ℝ) / (n + 1)) ^ m :=
        pow_le_pow_of_le_one hbase0 hbase1.le hle
  have hdiff0 : ∀ (i i' : Fin (n + 1)) (j : Fin (n + 1)),
      Tendsto (fun m => BdPt (φ m + 1) (V (φ m) i) j -
        BdPt (φ m + 1) (V (φ m) i') j) atTop (𝓝 0) := by
    intro i i' j
    have hle : ∀ m, |BdPt (φ m + 1) (V (φ m) i) j -
        BdPt (φ m + 1) (V (φ m) i') j| ≤ ((n : ℝ) / (n + 1)) ^ m :=
      fun m => hmesh i i' j m
    have hneg : Tendsto (fun m => -(((n : ℝ) / (n + 1)) ^ m)) atTop (𝓝 0) := by
      simpa using hpow0.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hpow0 ?_ ?_
    · exact Filter.Eventually.of_forall
        (fun m => (abs_le.mp (hle m)).1)
    · exact Filter.Eventually.of_forall
        (fun m => (abs_le.mp (hle m)).2)
  have hcoordR : ∀ (i : Fin (n + 1)) (j : Fin (n + 1)),
      Tendsto (fun m => BdPt (φ m + 1) (V (φ m) i) j) atTop
        (𝓝 ((A i).weights j)) := by
    intro i j
    have hcont : Continuous
        (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) => x.weights j) :=
      Convexity.StdSimplex.continuous_weights_apply (R := ℝ) j
    have h := (hcont.tendsto (A i)).comp (hcoord i)
    have hfun : ((fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) => x.weights j) ∘
        (fun m => X (φ m) i)) =
        (fun m => BdPt (φ m + 1) (V (φ m) i) j) := by
      funext m
      simp [hX, Function.comp_apply, BdSimp_weights]
    rw [hfun] at h
    exact h
  have hAgree : ∀ (i i' : Fin (n + 1)), A i = A i' := by
    intro i i'
    apply Convexity.StdSimplex.ext
    ext j
    have hsub : Tendsto (fun m => BdPt (φ m + 1) (V (φ m) i) j -
        BdPt (φ m + 1) (V (φ m) i') j) atTop
        (𝓝 ((A i).weights j - (A i').weights j)) :=
      (hcoordR i j).sub (hcoordR i' j)
    have h0 := hdiff0 i i' j
    have heq := tendsto_nhds_unique hsub h0
    exact sub_eq_zero.mp heq
  have hmemF : ∀ (i : Fin (n + 1)) (m : ℕ), X (φ m) i ∈ F i := by
    intro i m
    have hcov := BdLabel_mem_cover (F := F) (hF_cover := hF_cover)
      (S := Finset.univ) (hVvalid (φ m) i)
    have hlab := (hV (φ m) i).2
    rw [hlab] at hcov
    exact hcov
  set i₀ : Fin (n + 1) := ⟨0, Nat.zero_lt_succ n⟩ with hi₀
  refine ⟨A i₀, fun i => ?_⟩
  have hAi : A i = A i₀ := hAgree i i₀
  have hmem : A i ∈ F i :=
    (hF_closed i).mem_of_tendsto (hcoord i)
      (Filter.Eventually.of_forall (hmemF i))
  rw [hAi] at hmem
  exact hmem

end MathlibExt.Analysis.Convex.KKM
