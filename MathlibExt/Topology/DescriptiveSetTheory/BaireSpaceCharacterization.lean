/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.CantorScheme

@[expose] public section

section
/-!
# Baire space characterization
-/

noncomputable section

open Set Topology

namespace MathlibExt.Topology.DescriptiveSetTheory.BaireSpaceCharacterizationWanted

open Filter Metric EMetric

/-- **Zero-dimensional space.** A topological space $X$ is zero-dimensional if for every point
$x \in X$ and every open set $U \subseteq X$ containing $x$ there is a clopen set $V$ with
$x \in V \subseteq U$. -/
def IsZeroDimensionalSpace (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ (x : X) (U : Set X), IsOpen U → x ∈ U → ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U

/-- Every nonempty open set contains a point distinct from any given point of it.
Since singletons are compact, the compact-interior hypothesis rules out isolated points. -/
private theorem aux_noIsolated
    {X : Type*} [TopologicalSpace X]
    (hCompact : ∀ (K : Set X), IsCompact K → interior K = ∅)
    {x : X} {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ y ∈ U, y ≠ x := by
  by_contra hcon
  push Not at hcon
  have hsub : U ⊆ {x} := fun y hy => hcon y hy
  have hmem : ({x} : Set X) ∈ 𝓝 x := mem_of_superset (hU.mem_nhds hx) hsub
  have hint : x ∈ interior ({x} : Set X) := mem_interior_iff_mem_nhds.mpr hmem
  have hne : interior ({x} : Set X) ≠ ∅ := nonempty_iff_ne_empty.mp ⟨x, hint⟩
  exact hne (hCompact {x} isCompact_singleton)

/-- A clopen set containing two distinct points splits into two disjoint nonempty
clopen sets covering it. -/
private theorem aux_split_clopen
    {X : Type*} [TopologicalSpace X] [T1Space X]
    (hZero : IsZeroDimensionalSpace X)
    {V : Set X} (hV : IsClopen V) {x y : X} (hx : x ∈ V) (hy : y ∈ V) (hxy : x ≠ y) :
    ∃ A B : Set X, IsClopen A ∧ IsClopen B ∧ A.Nonempty ∧ B.Nonempty ∧
      Disjoint A B ∧ A ∪ B = V := by
  have hclosed : IsClosed ({y} : Set X) := isClosed_singleton
  have hopen : IsOpen ({y} : Set X)ᶜ := isOpen_compl_iff.mpr hclosed
  have hxmem : x ∈ ({y} : Set X)ᶜ := mem_compl_singleton_iff.mpr hxy
  obtain ⟨W, hWcl, hWx, hWsub⟩ := hZero x _ hopen hxmem
  refine ⟨V ∩ W, V \ W, hV.inter hWcl, hV.diff hWcl, ⟨x, hx, hWx⟩, ⟨y, ?_⟩, ?_,
    Set.inter_union_sdiff V W⟩
  · rw [Set.mem_sdiff]
    refine ⟨hy, fun hyW => ?_⟩
    have hmem : y ∈ ({y} : Set X)ᶜ := hWsub hyW
    simp at hmem
  · apply Set.disjoint_left.mpr
    rintro z ⟨hzV, hzW⟩ hzB
    rw [Set.mem_sdiff] at hzB
    exact hzB.2 hzW

/--
**Alexandrov–Urysohn theorem on Baire space.** Let $X$ be a nonempty Polish space that
is zero-dimensional (for every point $x$ and every open set $U$ containing $x$ there is a clopen
set $V$ with $x \in V \subseteq U$) and in which every compact subset has empty interior. Then $X$
is homeomorphic to the Baire space $\mathbb{N}^{\mathbb{N}}$ of all sequences of natural numbers,
with the product of the discrete topologies.

Proves `Wanted` entry `baire_space_characterization`.

Source: Alexandrov–Urysohn characterization; A. S. Kechris, Classical Descriptive Set Theory (1995),
Theorem 7.7.
-/
theorem baire_space_characterization
    {X : Type*} [TopologicalSpace X] [PolishSpace X] [Nonempty X]
    (hZero : IsZeroDimensionalSpace X)
    (hCompact : ∀ (K : Set X), IsCompact K → interior K = ∅) :
    Nonempty (X ≃ₜ (ℕ → ℕ)) := by
  -- Work with a compatible complete metric.
  let := TopologicalSpace.upgradeIsCompletelyMetrizable X
  let := Classical.decEq X
  -- Every neighborhood of a point contains a clopen neighborhood of small diameter.
  have hsmall : ∀ (x : X) (O : Set X), IsOpen O → x ∈ O → ∀ ε : ℝ, 0 < ε →
      ∃ W : Set X, IsClopen W ∧ x ∈ W ∧ W ⊆ O ∧
        Metric.ediam W ≤ 2 * ENNReal.ofReal ε := by
    intro x O hO hx ε hε
    have hball : IsOpen (O ∩ Metric.ball x ε) := hO.inter isOpen_ball
    have hmem : x ∈ O ∩ Metric.ball x ε :=
      ⟨hx, mem_ball.mpr (by rw [dist_self]; exact hε)⟩
    obtain ⟨W, hWcl, hWx, hWsub⟩ := hZero x _ hball hmem
    refine ⟨W, hWcl, hWx, hWsub.trans inter_subset_left, ?_⟩
    apply Metric.ediam_le
    intro a ha b hb
    have haε : dist a x < ε := mem_ball.mp (hWsub ha).2
    have hbε : dist b x < ε := mem_ball.mp (hWsub hb).2
    have hxb : dist x b < ε := by rw [dist_comm]; exact hbε
    have hdist : dist a b < 2 * ε := by
      calc dist a b ≤ dist a x + dist x b := dist_triangle _ _ _
      _ < ε + ε := add_lt_add haε hxb
      _ = 2 * ε := by ring
    have hle : ENNReal.ofReal (dist a b) ≤ ENNReal.ofReal (2 * ε) :=
      ENNReal.ofReal_le_ofReal (le_of_lt hdist)
    have h2 : ENNReal.ofReal (2 * ε) = 2 * ENNReal.ofReal ε := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      simp
    rw [h2] at hle
    rw [edist_dist]
    exact hle
  -- Every nonempty clopen set contains infinitely many disjoint nonempty clopen
  -- subsets of small diameter whose union is clopen.
  have hseq : ∀ (U : Set X), IsClopen U → U.Nonempty → ∀ ε : ℝ, 0 < ε →
      ∃ V : ℕ → Set X, (∀ n, IsClopen (V n)) ∧ (∀ n, (V n).Nonempty) ∧
        Pairwise (fun m n => Disjoint (V m) (V n)) ∧
        (∀ n, Metric.ediam (V n) ≤ 2 * ENNReal.ofReal ε) ∧
        IsClopen (⋃ n, V n) ∧ ⋃ n, V n ⊆ U := by
    intro U hU hUne ε hε
    have hUopen : IsOpen U := hU.isOpen
    have hUclosed : IsClosed U := hU.isClosed
    obtain ⟨x0, hx0⟩ := hUne
    have hUsub : interior U = U := interior_eq_iff_isOpen.mpr hUopen
    have hncomp : ¬ IsCompact U := by
      intro hc
      have hcon := hCompact U hc
      rw [hUsub] at hcon
      exact (nonempty_iff_ne_empty.mp ⟨x0, hx0⟩) hcon
    have hcompl : IsComplete U := hUclosed.isComplete
    have hntb : ¬ TotallyBounded U := by
      intro htb
      exact hncomp ((isCompact_iff_totallyBounded_isComplete).mpr ⟨htb, hcompl⟩)
    rw [Metric.totallyBounded_iff] at hntb
    push Not at hntb
    obtain ⟨ε₀, hε₀, hntb⟩ := hntb
    have hchoice : ∀ t : Finset X, ∃ y, y ∈ U ∧ ∀ x ∈ t, y ∉ Metric.ball x ε₀ := by
      intro t
      have hnot := hntb (↑t) (Finset.finite_toSet t)
      rw [not_subset] at hnot
      obtain ⟨y, hyU, hy⟩ := hnot
      refine ⟨y, hyU, fun x hx => ?_⟩
      simp only [mem_iUnion, Finset.mem_coe, not_exists] at hy
      exact hy x hx
    choose F hF using hchoice
    obtain ⟨s, hs0, hssucc⟩ : ∃ s : ℕ → Finset X,
        s 0 = ∅ ∧ ∀ n, s (n + 1) = insert (F (s n)) (s n) :=
      ⟨Nat.rec (motive := fun _ => Finset X) ∅ (fun _ prev => insert (F prev) prev),
        rfl, fun _ => rfl⟩
    have hmono : Monotone s := by
      apply monotone_nat_of_le_succ
      intro n
      rw [hssucc n]
      exact Finset.subset_insert _ _
    have hmem_seq : ∀ m n, m < n → F (s m) ∈ s n := by
      intro m n hmn
      have h1 : F (s m) ∈ s (m + 1) := by
        rw [hssucc m]
        exact Finset.mem_insert_self _ _
      exact hmono (Nat.succ_le_of_lt hmn) h1
    have hUmem : ∀ n, F (s n) ∈ U := fun n => (hF (s n)).1
    have hsep : ∀ m n, m ≠ n → ε₀ ≤ dist (F (s m)) (F (s n)) := by
      intro m n hmn
      rcases lt_or_gt_of_ne hmn with h | h
      · have hmem : F (s m) ∈ s n := hmem_seq m n h
        have hab := (hF (s n)).2 _ hmem
        rw [mem_ball] at hab
        rw [dist_comm]
        exact le_of_not_gt hab
      · have hmem : F (s n) ∈ s m := hmem_seq n m h
        have hab := (hF (s m)).2 _ hmem
        rw [mem_ball] at hab
        exact le_of_not_gt hab
    set r : ℝ := min (ε / 2) (ε₀ / 4) with hr
    have hrpos : 0 < r := lt_min (by linarith) (by linarith)
    have hrε : r ≤ ε := le_trans (min_le_left _ _) (by linarith)
    have hrε₀ : 2 * r < ε₀ := by
      have hle : r ≤ ε₀ / 4 := min_le_right _ _
      linarith
    have hW : ∀ n, ∃ W : Set X, IsClopen W ∧ F (s n) ∈ W ∧ W ⊆ U ∧
        W ⊆ Metric.ball (F (s n)) r ∧ Metric.ediam W ≤ 2 * ENNReal.ofReal ε := by
      intro n
      have hO : IsOpen (U ∩ Metric.ball (F (s n)) r) :=
        hUopen.inter isOpen_ball
      have hmem : F (s n) ∈ U ∩ Metric.ball (F (s n)) r := by
        refine ⟨hUmem n, mem_ball.mpr ?_⟩
        rw [dist_self]
        exact hrpos
      obtain ⟨W, hWcl, hWx, hWsub, hWdiam⟩ := hsmall _ _ hO hmem r hrpos
      refine ⟨W, hWcl, hWx, hWsub.trans inter_subset_left, ?_, ?_⟩
      · exact hWsub.trans inter_subset_right
      · calc Metric.ediam W ≤ 2 * ENNReal.ofReal r := hWdiam
          _ ≤ 2 * ENNReal.ofReal ε :=
            mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal hrε)
              (zero_le : (0 : ENNReal) ≤ 2)
    choose W hW using hW
    have hWcl : ∀ n, IsClopen (W n) := fun n => (hW n).1
    have hWmem : ∀ n, F (s n) ∈ W n := fun n => (hW n).2.1
    have hWU : ∀ n, W n ⊆ U := fun n => (hW n).2.2.1
    have hWball : ∀ n, W n ⊆ Metric.ball (F (s n)) r := fun n => (hW n).2.2.2.1
    have hWdiam : ∀ n, Metric.ediam (W n) ≤ 2 * ENNReal.ofReal ε :=
      fun n => (hW n).2.2.2.2
    have hdisj : Pairwise (fun m n => Disjoint (W m) (W n)) := by
      intro m n hmn
      show Disjoint (W m) (W n)
      apply Set.disjoint_left.mpr
      rintro a ham han
      have ham' : dist a (F (s m)) < r := mem_ball.mp (hWball m ham)
      have han' : dist a (F (s n)) < r := mem_ball.mp (hWball n han)
      have e1 : dist (F (s m)) a < r := by rw [dist_comm]; exact ham'
      have htri : dist (F (s m)) (F (s n)) < 2 * r := by
        calc dist (F (s m)) (F (s n))
            ≤ dist (F (s m)) a + dist a (F (s n)) := dist_triangle _ _ _
          _ < r + r := add_lt_add e1 han'
          _ = 2 * r := by ring
      have hsep' := hsep m n hmn
      linarith
    have hnbhd : ∀ (z : X) (t : ℝ), 0 < t → Metric.ball z t ∈ 𝓝 z :=
      fun z t ht => isOpen_ball.mem_nhds (mem_ball.mpr (by rwa [dist_self]))
    set s₀ : ℝ := (ε₀ / 2 - r) / 2 with hs₀def
    have hs₀pos : 0 < s₀ := by rw [hs₀def]; linarith
    have hs₀rel : 2 * s₀ = ε₀ / 2 - r := by rw [hs₀def]; ring
    have hloc : LocallyFinite (fun n => Metric.closedBall (F (s n)) r) := by
      intro z
      refine ⟨Metric.ball z s₀, hnbhd z s₀ hs₀pos, ?_⟩
      have hfin : {(n : ℕ) |
          (Metric.closedBall (F (s n)) r ∩ Metric.ball z s₀).Nonempty}.Subsingleton := by
        intro n hn m hm
        obtain ⟨a, ha⟩ := hn
        obtain ⟨b, hb⟩ := hm
        have ha1 : dist a z < s₀ := mem_ball.mp ha.2
        have ha2 : dist a (F (s n)) ≤ r := Metric.mem_closedBall.mp ha.1
        have hb1 : dist b z < s₀ := mem_ball.mp hb.2
        have hb2 : dist b (F (s m)) ≤ r := Metric.mem_closedBall.mp hb.1
        have d1 : dist (F (s n)) a ≤ r := by rw [dist_comm]; exact ha2
        have d3 : dist z b < s₀ := by rw [dist_comm]; exact hb1
        have t1 : dist (F (s n)) (F (s m)) ≤ dist (F (s n)) a + dist a (F (s m)) :=
          dist_triangle _ _ _
        have t2 : dist a (F (s m)) ≤ dist a z + dist z (F (s m)) :=
          dist_triangle _ _ _
        have t3 : dist z (F (s m)) ≤ dist z b + dist b (F (s m)) :=
          dist_triangle _ _ _
        have d2 : dist a z < s₀ := ha1
        by_contra hne
        have hsep' := hsep n m hne
        linarith
      exact hfin.finite
    have hWloc : LocallyFinite W := by
      intro z
      obtain ⟨U₀, hU₀, hfin⟩ := hloc z
      refine ⟨U₀, hU₀, ?_⟩
      apply Finite.subset hfin
      intro n hn
      obtain ⟨a, ha⟩ := hn
      exact ⟨a, Set.inter_subset_inter
        ((hWball n).trans ball_subset_closedBall) Subset.rfl ha⟩
    have hunion_closed : IsClosed (⋃ n, W n) :=
      hWloc.isClosed_iUnion (fun n => (hWcl n).isClosed)
    have hunion_open : IsOpen (⋃ n, W n) :=
      isOpen_iUnion (fun n => (hWcl n).isOpen)
    exact ⟨W, hWcl, fun n => ⟨F (s n), hWmem n⟩, hdisj, hWdiam,
      ⟨hunion_closed, hunion_open⟩, iUnion_subset_iff.mpr (fun n => hWU n)⟩
  -- Every nonempty clopen set partitions into countably infinitely many disjoint
  -- nonempty clopen subsets of small diameter.
  have hpart : ∀ (U : Set X), IsClopen U → U.Nonempty → ∀ ε : ℝ, 0 < ε →
      ∃ C : ℕ → Set X, (∀ n, IsClopen (C n)) ∧ (∀ n, (C n).Nonempty) ∧
        Pairwise (fun m n => Disjoint (C m) (C n)) ∧
        (∀ n, Metric.ediam (C n) ≤ 2 * ENNReal.ofReal ε) ∧ ⋃ n, C n = U := by
      intro U hU hUne ε hε
      obtain ⟨V, hVcl, hVne, hVdisj, hVdiam, hVunioncl, hVunionU⟩ :=
        hseq U hU hUne ε hε
      set R : Set X := U \ ⋃ n, V n with hRdef
      have hRcl : IsClopen R := hU.diff hVunioncl
      have hRU : R ⊆ U := fun x hx => ((Set.mem_sdiff x).mp hx).1
      -- Cover R by small clopen sets.
      have hcov : ∀ z : ↥R, ∃ W : Set X, IsClopen W ∧ z.val ∈ W ∧ W ⊆ R ∧
          Metric.ediam W ≤ 2 * ENNReal.ofReal ε := by
        intro z
        obtain ⟨W, hWcl, hWx, hWsub, hWdiam⟩ :=
          hsmall z.val R hRcl.isOpen z.property ε hε
        exact ⟨W, hWcl, hWx, hWsub, hWdiam⟩
      choose W hW using hcov
      -- Countable subcover via a countable basis of the subtype.
      obtain ⟨bR, hbRcount, -, hbRbasis⟩ := TopologicalSpace.exists_countable_basis ↥R
      have henc : Encodable ↥bR := Countable.toEncodable hbRcount
      -- For each basis element, pick a cover member containing it (or junk).
      have hsel : ∀ B : ↥bR, ∃ W0 : Set X, IsClopen W0 ∧ W0 ⊆ R ∧
          Metric.ediam W0 ≤ 2 * ENNReal.ofReal ε ∧
          ((∃ z' : ↥R, B.val ⊆ Subtype.val ⁻¹' W z') →
            B.val ⊆ Subtype.val ⁻¹' W0) := by
        intro B
        by_cases hgood : ∃ z' : ↥R, B.val ⊆ Subtype.val ⁻¹' W z'
        · obtain ⟨z', hz'⟩ := hgood
          exact ⟨W z', (hW z').1, (hW z').2.2.1, (hW z').2.2.2, fun _ => hz'⟩
        · refine ⟨∅, isClopen_empty, empty_subset _, ?_, fun h => absurd h hgood⟩
          calc Metric.ediam (∅ : Set X) = 0 := Metric.ediam_empty
            _ ≤ 2 * ENNReal.ofReal ε := (zero_le : (0 : ENNReal) ≤ _)
      choose g hg using hsel
      -- Index the selected sets by ℕ.
      set f : ℕ → Set X := fun n => match Encodable.decode (α := ↥bR) n with
        | none => ∅
        | some B => g B with hfdef
      have hf : ∀ n, IsClopen (f n) ∧ f n ⊆ R ∧
          Metric.ediam (f n) ≤ 2 * ENNReal.ofReal ε ∧
          (∀ B : ↥bR, Encodable.decode (α := ↥bR) n = some B → f n = g B) := by
        intro n
        have hdec : ∀ o : Option ↥bR, Encodable.decode (α := ↥bR) n = o →
            IsClopen (match o with | none => (∅ : Set X) | some B => g B) ∧
            (match o with | none => (∅ : Set X) | some B => g B) ⊆ R ∧
            Metric.ediam (match o with | none => (∅ : Set X) | some B => g B) ≤
              2 * ENNReal.ofReal ε ∧
            (∀ B : ↥bR, o = some B →
              (match o with | none => (∅ : Set X) | some C => g C) = g B) := by
          intro o ho
          cases o with
          | none =>
            refine ⟨isClopen_empty, empty_subset _, ?_, fun B hB => ?_⟩
            · calc Metric.ediam (∅ : Set X) = 0 := Metric.ediam_empty
                _ ≤ 2 * ENNReal.ofReal ε := (zero_le : (0 : ENNReal) ≤ _)
            · simp at hB
          | some B =>
            refine ⟨(hg B).1, (hg B).2.1, (hg B).2.2.1, fun B' hB' => ?_⟩
            have hBB : B = B' := Option.some_inj.mp hB'
            subst hBB
            rfl
        have hmain := hdec (Encodable.decode (α := ↥bR) n) rfl
        have hfeq : f n =
            (match Encodable.decode (α := ↥bR) n with
              | none => (∅ : Set X) | some B => g B) := rfl
        rw [hfeq]
        exact hmain
      have hfcl : ∀ n, IsClopen (f n) := fun n => (hf n).1
      have hfR : ∀ n, f n ⊆ R := fun n => (hf n).2.1
      have hfdiam : ∀ n, Metric.ediam (f n) ≤ 2 * ENNReal.ofReal ε :=
        fun n => (hf n).2.2.1
      have hfeq : ∀ (n : ℕ) (B : ↥bR), Encodable.decode (α := ↥bR) n = some B →
          f n = g B := fun n B h => (hf n).2.2.2 B h
      -- The selected sets cover R.
      have hfcov : ⋃ n, f n = R := by
        apply le_antisymm (iUnion_subset_iff.mpr hfR)
        intro x hx
        have hzx : (⟨x, hx⟩ : ↥R) ∈ Subtype.val ⁻¹' W ⟨x, hx⟩ := (hW ⟨x, hx⟩).2.1
        have hopen : IsOpen (Subtype.val ⁻¹' W ⟨x, hx⟩ : Set ↥R) :=
          (hW ⟨x, hx⟩).1.isOpen.preimage continuous_subtype_val
        obtain ⟨B, hBbR, hzB, hBsub⟩ :=
          hbRbasis.exists_subset_of_mem_open hzx hopen
        obtain ⟨q, rfl⟩ : ∃ q : ↥bR, q.val = B := ⟨⟨B, hBbR⟩, rfl⟩
        have hgood : ∃ z' : ↥R, q.val ⊆ Subtype.val ⁻¹' W z' := ⟨⟨x, hx⟩, hBsub⟩
        have hcover : q.val ⊆ Subtype.val ⁻¹' g q := (hg q).2.2.2 hgood
        have hmem : (⟨x, hx⟩ : ↥R) ∈ Subtype.val ⁻¹' g q := hcover hzB
        have hn : f (Encodable.encode q) = g q := hfeq _ _ (Encodable.encodek _)
        refine mem_iUnion.mpr ⟨Encodable.encode q, ?_⟩
        rw [hn]
        exact hmem
      -- Disjointify the cover.
      have hmemU : ∀ {n : ℕ} {x : X}, x ∈ ⋃ k ∈ Finset.range n, f k →
          ∃ k, k < n ∧ x ∈ f k := by
        intro n x hx
        rw [mem_iUnion] at hx
        obtain ⟨k, hk⟩ := hx
        rw [mem_iUnion] at hk
        obtain ⟨hkr, hxk⟩ := hk
        exact ⟨k, Finset.mem_range.mp hkr, hxk⟩
      have hsubU : ∀ (n m : ℕ), m < n → f m ⊆ ⋃ k ∈ Finset.range n, f k := by
        intro n m hmn x hx
        rw [mem_iUnion]
        refine ⟨m, mem_iUnion.mpr ⟨Finset.mem_range.mpr hmn, hx⟩⟩
      set D : ℕ → Set X := fun n => f n \ ⋃ k ∈ Finset.range n, f k with hDdef
      have hDcl : ∀ n, IsClopen (D n) := by
        intro n
        change IsClopen (f n \ ⋃ k ∈ Finset.range n, f k)
        exact (hfcl n).diff (isClopen_biUnion_finset (fun k _ => hfcl k))
      have hDsub : ∀ n, D n ⊆ f n := by
        intro n x hx
        have hx' : x ∈ f n \ ⋃ k ∈ Finset.range n, f k := hx
        exact ((Set.mem_sdiff x).mp hx').1
      have hDdiam : ∀ n, Metric.ediam (D n) ≤ 2 * ENNReal.ofReal ε := by
        intro n
        exact le_trans (Metric.ediam_mono (hDsub n)) (hfdiam n)
      have hDdisj : Pairwise (fun m n => Disjoint (D m) (D n)) := by
        intro m n hmn
        show Disjoint (D m) (D n)
        rcases lt_or_gt_of_ne hmn with h | h
        · apply Set.disjoint_left.mpr
          rintro x hx1 hx2
          have e1 : x ∈ f m := hDsub m hx1
          have hx2' : x ∈ f n \ ⋃ k ∈ Finset.range n, f k := hx2
          have e2 := ((Set.mem_sdiff x).mp hx2').2
          exact e2 (hsubU n m h e1)
        · apply Set.disjoint_left.mpr
          rintro x hx1 hx2
          have e1 : x ∈ f n := hDsub n hx2
          have hx1' : x ∈ f m \ ⋃ k ∈ Finset.range m, f k := hx1
          have e2 := ((Set.mem_sdiff x).mp hx1').2
          exact e2 (hsubU m n h e1)
      have hDunion : ⋃ n, D n = R := by
        apply le_antisymm
        · apply iUnion_subset_iff.mpr
          intro n
          exact le_trans (hDsub n) (hfR n)
        · rw [← hfcov]
          apply iUnion_subset_iff.mpr
          intro m x hxm
          classical
          have hne : ∃ n, x ∈ f n := ⟨m, hxm⟩
          have hm₀mem : x ∈ f (Nat.find hne) := Nat.find_spec hne
          have hDmem : x ∈ D (Nat.find hne) := by
            have h1 : x ∈ f (Nat.find hne) \
                ⋃ k ∈ Finset.range (Nat.find hne), f k := by
              apply (Set.mem_sdiff x).mpr
              refine ⟨hm₀mem, fun hcon => ?_⟩
              obtain ⟨k, hkn, hxk⟩ := hmemU hcon
              have hle : Nat.find hne ≤ k := Nat.find_min' hne hxk
              omega
            exact h1
          exact mem_iUnion.mpr ⟨_, hDmem⟩
      have hVDsub : ∀ n, V n ∪ D n ⊆ U := by
        intro n
        apply Set.union_subset_iff.mpr
        refine ⟨(subset_iUnion V n).trans hVunionU,
          (hDsub n).trans ((hfR n).trans hRU)⟩
      have hkey : ∀ a b, a ≠ b → Disjoint (V a ∪ D a) (V b ∪ D b) := by
        intro a b hab
        apply Set.disjoint_left.mpr
        rintro x hx1 hx2
        rw [mem_union] at hx1 hx2
        rcases hx1 with hVa | hDa
        · rcases hx2 with hVb | hDb
          · exact (Set.disjoint_left.mp (hVdisj hab) hVa) hVb
          · exact ((Set.mem_sdiff x).mp ((hfR b) ((hDsub b) hDb))).2
              (subset_iUnion V a hVa)
        · rcases hx2 with hVb | hDb
          · exact ((Set.mem_sdiff x).mp ((hfR a) ((hDsub a) hDa))).2
              (subset_iUnion V b hVb)
          · exact (Set.disjoint_left.mp (hDdisj hab) hDa) hDb
      have hVDdisj' : ∀ n, Disjoint (V n) (D n) := by
        intro n
        apply Set.disjoint_left.mpr
        intro x hxV hxD
        exact ((Set.mem_sdiff x).mp ((hfR n) ((hDsub n) hxD))).2
          (subset_iUnion V n hxV)
      -- Split each V n ∪ D n into two nonempty clopen pieces.
      have hpair : ∀ n, ∃ P Q : Set X, IsClopen P ∧ IsClopen Q ∧ P.Nonempty ∧
          Q.Nonempty ∧ Disjoint P Q ∧ P ∪ Q = V n ∪ D n ∧
          Metric.ediam P ≤ 2 * ENNReal.ofReal ε ∧
          Metric.ediam Q ≤ 2 * ENNReal.ofReal ε := by
        intro n
        by_cases hD : (D n).Nonempty
        · exact ⟨V n, D n, hVcl n, hDcl n, hVne n, hD, hVDdisj' n, rfl,
            hVdiam n, hDdiam n⟩
        · have hempty : D n = ∅ := Set.not_nonempty_iff_eq_empty.mp hD
          obtain ⟨xV, hxV⟩ := hVne n
          obtain ⟨yV, hyV, hyne⟩ :=
            aux_noIsolated hCompact (hVcl n).isOpen hxV
          obtain ⟨A, B, hAcl, hBcl, hAne, hBne, hABdisj, hABunion⟩ :=
            aux_split_clopen hZero (hVcl n) hxV hyV (Ne.symm hyne)
          refine ⟨A, B, hAcl, hBcl, hAne, hBne, hABdisj, ?_, ?_, ?_⟩
          · rw [hempty, union_empty]
            exact hABunion
          · exact le_trans (Metric.ediam_mono
              (subset_union_left.trans (le_of_eq hABunion))) (hVdiam n)
          · exact le_trans (Metric.ediam_mono
              (subset_union_right.trans (le_of_eq hABunion))) (hVdiam n)
      choose P Q hPQ using hpair
      have hPcl : ∀ n, IsClopen (P n) := fun n => (hPQ n).1
      have hQcl : ∀ n, IsClopen (Q n) := fun n => (hPQ n).2.1
      have hPne : ∀ n, (P n).Nonempty := fun n => (hPQ n).2.2.1
      have hQne : ∀ n, (Q n).Nonempty := fun n => (hPQ n).2.2.2.1
      have hPQdisj : ∀ n, Disjoint (P n) (Q n) := fun n => (hPQ n).2.2.2.2.1
      have hPQunion : ∀ n, P n ∪ Q n = V n ∪ D n := fun n => (hPQ n).2.2.2.2.2.1
      have hPdiam : ∀ n, Metric.ediam (P n) ≤ 2 * ENNReal.ofReal ε :=
        fun n => (hPQ n).2.2.2.2.2.2.1
      have hQdiam : ∀ n, Metric.ediam (Q n) ≤ 2 * ENNReal.ofReal ε :=
        fun n => (hPQ n).2.2.2.2.2.2.2
      have hsubP : ∀ k, P k ⊆ V k ∪ D k :=
        fun k => subset_union_left.trans (le_of_eq (hPQunion k))
      have hsubQ : ∀ k, Q k ⊆ V k ∪ D k :=
        fun k => subset_union_right.trans (le_of_eq (hPQunion k))
      set E : ℕ → Set X := fun m => if m % 2 = 0 then P (m / 2) else Q (m / 2)
        with hEdef
      have hE : ∀ m, (m % 2 = 0 ∧ E m = P (m / 2)) ∨
          (m % 2 = 1 ∧ E m = Q (m / 2)) := by
        intro m
        by_cases h : m % 2 = 0
        · exact Or.inl ⟨h, by simp [hEdef, h]⟩
        · have h1 : m % 2 = 1 := by omega
          exact Or.inr ⟨h1, by simp [hEdef, h]⟩
      have hEeven : ∀ k, E (2 * k) = P k := by
        intro k
        rcases hE (2 * k) with ⟨-, hEq⟩ | ⟨h1, -⟩
        · have hk : (2 * k) / 2 = k := by omega
          rw [hk] at hEq
          exact hEq
        · exfalso
          omega
      have hEodd : ∀ k, E (2 * k + 1) = Q k := by
        intro k
        rcases hE (2 * k + 1) with ⟨h0, -⟩ | ⟨-, hEq⟩
        · exfalso
          omega
        · have hk : (2 * k + 1) / 2 = k := by omega
          rw [hk] at hEq
          exact hEq
      have hEPQ : ∀ m, E m ⊆ V (m / 2) ∪ D (m / 2) := by
        intro m
        rcases hE m with ⟨-, hEq⟩ | ⟨-, hEq⟩
        · rw [hEq]
          exact hsubP _
        · rw [hEq]
          exact hsubQ _
      have hEcl : ∀ m, IsClopen (E m) := by
        intro m
        rcases hE m with ⟨-, hEq⟩ | ⟨-, hEq⟩
        · rw [hEq]; exact hPcl _
        · rw [hEq]; exact hQcl _
      have hEne : ∀ m, (E m).Nonempty := by
        intro m
        rcases hE m with ⟨-, hEq⟩ | ⟨-, hEq⟩
        · rw [hEq]; exact hPne _
        · rw [hEq]; exact hQne _
      have hEdiam : ∀ m, Metric.ediam (E m) ≤ 2 * ENNReal.ofReal ε := by
        intro m
        rcases hE m with ⟨-, hEq⟩ | ⟨-, hEq⟩
        · rw [hEq]; exact hPdiam _
        · rw [hEq]; exact hQdiam _
      have hEdisj : Pairwise (fun m n => Disjoint (E m) (E n)) := by
        intro i j hij
        show Disjoint (E i) (E j)
        rcases hE i with ⟨hi0, hEi⟩ | ⟨hi1, hEi⟩ <;>
          rcases hE j with ⟨hj0, hEj⟩ | ⟨hj1, hEj⟩
        · rw [hEi, hEj]
          by_cases h : i / 2 = j / 2
          · exfalso
            apply hij
            omega
          · exact ((hkey _ _ h).mono_left (hsubP _)).mono_right (hsubP _)
        · rw [hEi, hEj]
          by_cases h : i / 2 = j / 2
          · rw [h]
            exact hPQdisj _
          · exact ((hkey _ _ h).mono_left (hsubP _)).mono_right (hsubQ _)
        · rw [hEi, hEj]
          by_cases h : i / 2 = j / 2
          · rw [h]
            exact (hPQdisj _).symm
          · exact ((hkey _ _ h).mono_left (hsubQ _)).mono_right (hsubP _)
        · rw [hEi, hEj]
          by_cases h : i / 2 = j / 2
          · exfalso
            apply hij
            omega
          · exact ((hkey _ _ h).mono_left (hsubQ _)).mono_right (hsubQ _)
      have hEunion : ⋃ m, E m = U := by
        apply le_antisymm
        · apply iUnion_subset_iff.mpr
          intro m
          exact (hEPQ m).trans (hVDsub (m / 2))
        · intro x hx
          by_cases hxV : x ∈ ⋃ n, V n
          · obtain ⟨k, hk⟩ := mem_iUnion.mp hxV
            have hVk : V k ⊆ P k ∪ Q k := by
              rw [hPQunion k]
              exact subset_union_left
            have hmemPQ := hVk hk
            rw [mem_union] at hmemPQ
            rcases hmemPQ with hPx | hQx
            · refine mem_iUnion.mpr ⟨2 * k, ?_⟩
              rw [hEeven]
              exact hPx
            · refine mem_iUnion.mpr ⟨2 * k + 1, ?_⟩
              rw [hEodd]
              exact hQx
          · have hRx : x ∈ R := ⟨hx, hxV⟩
            have hDx : x ∈ ⋃ n, D n := by
              rw [hDunion]
              exact hRx
            obtain ⟨m, hm⟩ := mem_iUnion.mp hDx
            have hmem : x ∈ P m ∪ Q m := by
              have hsub : D m ⊆ P m ∪ Q m := by
                rw [hPQunion m]
                exact subset_union_right
              exact hsub hm
            rw [mem_union] at hmem
            rcases hmem with hPx | hQx
            · refine mem_iUnion.mpr ⟨2 * m, ?_⟩
              rw [hEeven]
              exact hPx
            · refine mem_iUnion.mpr ⟨2 * m + 1, ?_⟩
              rw [hEodd]
              exact hQx
      exact ⟨E, hEcl, hEne, hEdisj, hEdiam, hEunion⟩
  -- Package the partition for uniform choice.
  have hpart' : ∀ (U : Set X) (ε : ℝ), ∃ C : ℕ → Set X,
      (U.Nonempty → IsClopen U → 0 < ε →
        ((∀ n, IsClopen (C n)) ∧ (∀ n, (C n).Nonempty) ∧
          Pairwise (fun m n => Disjoint (C m) (C n)) ∧
          (∀ n, Metric.ediam (C n) ≤ 2 * ENNReal.ofReal ε) ∧ ⋃ n, C n = U)) := by
    intro U ε
    by_cases h : U.Nonempty ∧ IsClopen U ∧ 0 < ε
    · obtain ⟨hne, hcl, hpos⟩ := h
      obtain ⟨C, hC⟩ := hpart U hcl hne ε hpos
      exact ⟨C, fun _ _ _ => hC⟩
    · refine ⟨fun _ => univ, fun hne hcl hpos => absurd ⟨hne, hcl, hpos⟩ h⟩
  choose C hC using hpart'
  -- The Lusin scheme.
  set A : List ℕ → Set X := List.rec univ
    (fun a t IH => C IH ((1 / 2 : ℝ) ^ (t.length + 1)) a) with hAdef
  have hAnil : A [] = univ := rfl
  have hAcons : ∀ (a : ℕ) (t : List ℕ),
      A (a :: t) = C (A t) ((1 / 2 : ℝ) ^ (t.length + 1)) a := fun _ _ => rfl
  have hAgood : ∀ l : List ℕ, (A l).Nonempty ∧ IsClopen (A l) := by
    intro l
    induction l with
    | nil => exact ⟨univ_nonempty, isClopen_univ⟩
    | cons a t IH =>
      rw [hAcons]
      have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (t.length + 1) :=
        pow_pos (by norm_num) _
      exact ⟨(hC _ _ IH.1 IH.2 hpos).2.1 a, (hC _ _ IH.1 IH.2 hpos).1 a⟩
  have hAunion : ∀ l : List ℕ, ⋃ a, A (a :: l) = A l := by
    intro l
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (l.length + 1) := pow_pos (by norm_num) _
    have hgood := hC (A l) _ (hAgood l).1 (hAgood l).2 hpos
    have heq : (fun a => A (a :: l)) = C (A l) ((1 / 2 : ℝ) ^ (l.length + 1)) :=
      funext (fun a => hAcons a l)
    rw [heq]
    exact hgood.2.2.2.2
  have hAsub : ∀ (l : List ℕ) (a : ℕ), A (a :: l) ⊆ A l := by
    intro l a
    calc A (a :: l) ⊆ ⋃ a, A (a :: l) := subset_iUnion (fun a => A (a :: l)) a
    _ = A l := hAunion l
  have hAanti : CantorScheme.ClosureAntitone A := by
    intro l a
    have hcl : IsClosed (A (a :: l)) := (hAgood (a :: l)).2.isClosed
    rw [hcl.closure_eq]
    exact hAsub l a
  have hAdisj : CantorScheme.Disjoint A := by
    intro l a b hab
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (l.length + 1) := pow_pos (by norm_num) _
    have hgood := hC (A l) _ (hAgood l).1 (hAgood l).2 hpos
    have e1 : A (a :: l) = C (A l) ((1 / 2 : ℝ) ^ (l.length + 1)) a := hAcons a l
    have e2 : A (b :: l) = C (A l) ((1 / 2 : ℝ) ^ (l.length + 1)) b := hAcons b l
    rw [e1, e2]
    exact hgood.2.2.1 hab
  have hBlim : Filter.Tendsto (fun n : ℕ => 2 * ENNReal.ofReal ((1 / 2 : ℝ) ^ n))
      Filter.atTop (nhds 0) := by
    have hpow : Filter.Tendsto (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h0 : Filter.Tendsto (fun n : ℕ => 2 * ((1 / 2 : ℝ) ^ n)) Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hpow
    have h2 : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal (2 * ((1 / 2 : ℝ) ^ n)))
        Filter.atTop (nhds (ENNReal.ofReal 0)) :=
      (ENNReal.continuous_ofReal.tendsto 0).comp h0
    have heq : ∀ n : ℕ, ENNReal.ofReal (2 * ((1 / 2 : ℝ) ^ n)) =
        2 * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
      intro n
      rw [ENNReal.ofReal_mul (by norm_num)]
      simp
    simpa [heq] using h2
  have hedge : ∀ (x : ℕ → ℕ) (n : ℕ), 1 ≤ n →
      Metric.ediam (A (PiNat.res x n)) ≤ 2 * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
    intro x n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hlen : (PiNat.res x k).length = k := PiNat.res_length x k
    have hres : PiNat.res x (k + 1) = x k :: PiNat.res x k := PiNat.res_succ x k
    rw [hres, hAcons, hlen]
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 1) := pow_pos (by norm_num) _
    exact (hC (A (PiNat.res x k)) _ ((hAgood _).1) ((hAgood _).2) hpos).2.2.2.1 (x k)
  have hVdiam : CantorScheme.VanishingDiam A := by
    intro x
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBlim
    · apply Filter.Eventually.of_forall
      intro n
      exact zero_le
    · rw [Filter.eventually_atTop]
      refine ⟨1, fun n hn => ?_⟩
      exact hedge x n hn
  have hdom : (CantorScheme.inducedMap A).1 = Set.univ :=
    hAanti.map_of_vanishingDiam hVdiam (fun l => (hAgood l).1)
  have hsame : ∀ (n : ℕ) (l₁ l₂ : List ℕ), l₁.length = n → l₂.length = n →
      l₁ ≠ l₂ → Disjoint (A l₁) (A l₂) := by
    intro n
    induction n with
    | zero =>
      intro l₁ l₂ h1 h2 hne
      rw [List.length_eq_zero_iff.mp h1, List.length_eq_zero_iff.mp h2] at hne
      exact absurd rfl hne
    | succ n IH =>
      intro l₁ l₂ h1 h2 hne
      cases l₁ with
      | nil => simp at h1
      | cons a₁ t₁ =>
        cases l₂ with
        | nil => simp at h2
        | cons a₂ t₂ =>
          simp only [List.length_cons] at h1 h2
          have ht1 : t₁.length = n := by omega
          have ht2 : t₂.length = n := by omega
          by_cases ht : t₁ = t₂
          · rw [ht] at hne ⊢
            have ha : a₁ ≠ a₂ := fun h => hne (by rw [h])
            have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (t₂.length + 1) :=
              pow_pos (by norm_num) _
            have hgood := hC (A t₂) _ ((hAgood _).1) ((hAgood _).2) hpos
            have e1 : A (a₁ :: t₂) = C (A t₂) ((1 / 2 : ℝ) ^ (t₂.length + 1)) a₁ :=
              hAcons a₁ t₂
            have e2 : A (a₂ :: t₂) = C (A t₂) ((1 / 2 : ℝ) ^ (t₂.length + 1)) a₂ :=
              hAcons a₂ t₂
            rw [e1, e2]
            exact hgood.2.2.1 ha
          · exact ((IH t₁ t₂ ht1 ht2 ht).mono_left (hAsub t₁ a₁)).mono_right
              (hAsub t₂ a₂)
  have hres_sub : ∀ (x : ℕ → ℕ) (k n : ℕ), k ≤ n →
      A (PiNat.res x n) ⊆ A (PiNat.res x k) := by
    intro x k n hkn
    have hstep : ∀ j, A (PiNat.res x (j + 1)) ⊆ A (PiNat.res x j) := by
      intro j
      rw [PiNat.res_succ]
      exact hAsub _ _
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
    clear hkn
    induction d with
    | zero =>
      simp only [Nat.add_zero]
      exact Subset.rfl
    | succ d IH =>
      have e1 : k + (d + 1) = (k + d) + 1 := by omega
      rw [e1]
      exact le_trans (hstep _) IH
  have hfiber : ∀ (x : ℕ → ℕ) (a b : X), a ∈ ⋂ n, A (PiNat.res x n) →
      b ∈ ⋂ n, A (PiNat.res x n) → a = b := by
    intro x a b ha hb
    rw [mem_iInter] at ha hb
    apply eq_of_edist_eq_zero
    have hle : ∀ n, 1 ≤ n →
        edist a b ≤ 2 * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
      intro n hn
      exact le_trans (Metric.edist_le_ediam_of_mem (ha n) (hb n)) (hedge x n hn)
    by_contra hne
    have hpos : (0 : ENNReal) < edist a b := pos_iff_ne_zero.mpr hne
    have hev : ∀ᶠ n in Filter.atTop, 2 * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) < edist a b :=
      hBlim.eventually (Iio_mem_nhds hpos)
    have hev1 : ∀ᶠ n in Filter.atTop, 1 ≤ n := eventually_ge_atTop 1
    obtain ⟨n, hn1, hn2⟩ := (hev.and hev1).exists
    exact lt_irrefl _ (lt_of_le_of_lt (hle n hn2) hn1)
  -- The map from Baire space.
  have hFdef : ∀ x : ℕ → ℕ, x ∈ (CantorScheme.inducedMap A).1 := by
    intro x
    rw [hdom]
    exact mem_univ x
  set F : (ℕ → ℕ) → X := fun x => (CantorScheme.inducedMap A).2 ⟨x, hFdef x⟩ with hFdef2
  have hFmem : ∀ (x : ℕ → ℕ) (n : ℕ), F x ∈ A (PiNat.res x n) := by
    intro x n
    have h := CantorScheme.map_mem (A := A) (⟨x, hFdef x⟩ : (CantorScheme.inducedMap A).1) n
    change (CantorScheme.inducedMap A).2 ⟨x, hFdef x⟩ ∈ A (PiNat.res x n)
    exact h
  have hFcont : Continuous F := by
    have hgc : Continuous (CantorScheme.inducedMap A).2 := hVdiam.map_continuous
    have hsec : Continuous
        (fun x : ℕ → ℕ => (⟨x, hFdef x⟩ : (CantorScheme.inducedMap A).1)) :=
      Continuous.subtype_mk continuous_id _
    change Continuous ((CantorScheme.inducedMap A).2 ∘
      fun x : ℕ → ℕ => (⟨x, hFdef x⟩ : (CantorScheme.inducedMap A).1))
    exact hgc.comp hsec
  have hFinj : Function.Injective F := by
    intro x y hxy
    have h : (⟨x, hFdef x⟩ : (CantorScheme.inducedMap A).1) = ⟨y, hFdef y⟩ :=
      hAdisj.map_injective hxy
    exact congrArg Subtype.val h
  -- Branches through any scheme with the covering property.
  have hroot' : ∀ (B : List ℕ → Set X), (∀ t, ⋃ c, B (c :: t) = B t) →
      ∀ (y : X), y ∈ B [] → ∃ w : ℕ → ℕ, ∀ k, y ∈ B (PiNat.res w k) := by
    intro B hBunion y hy
    have hstep : ∀ t : List ℕ, ∃ a, y ∈ B t → y ∈ B (a :: t) := by
      intro t
      by_cases ht : y ∈ B t
      · rw [← hBunion t] at ht
        obtain ⟨a, ha⟩ := mem_iUnion.mp ht
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h => absurd h ht⟩
    choose g hg using hstep
    set L : ℕ → List ℕ := fun k => Nat.rec (motive := fun _ => List ℕ) []
      (fun _ prev => g prev :: prev) k with hLdef
    have hLmem : ∀ k, y ∈ B (L k) := by
      intro k
      induction k with
      | zero => exact hy
      | succ k IH => exact hg _ IH
    set w : ℕ → ℕ := fun n => g (L n) with hwdef
    have hres : ∀ k, PiNat.res w k = L k := by
      intro k
      induction k with
      | zero => rfl
      | succ k IH =>
        rw [PiNat.res_succ, IH]
    exact ⟨w, fun k => by rw [hres k]; exact hLmem k⟩
  have hFsurj : Function.Surjective F := by
    intro y
    have hy : y ∈ A [] := by
      rw [hAnil]
      exact mem_univ y
    obtain ⟨z, hz⟩ := hroot' A hAunion y hy
    refine ⟨z, ?_⟩
    have h1 : F z ∈ ⋂ k, A (PiNat.res z k) := mem_iInter.mpr (hFmem z)
    have h2 : y ∈ ⋂ k, A (PiNat.res z k) := mem_iInter.mpr hz
    exact hfiber z _ _ h1 h2
  have him : ∀ (x : ℕ → ℕ) (n : ℕ),
      F '' (PiNat.cylinder x n) = A (PiNat.res x n) := by
    intro x n
    apply Subset.antisymm
    · rintro y ⟨z, hz, rfl⟩
      have hres : PiNat.res z n = PiNat.res x n := PiNat.res_eq_res.mpr hz
      have hmem := hFmem z n
      rw [hres] at hmem
      exact hmem
    · intro y hy
      set l₀ : List ℕ := PiNat.res x n with hl₀def
      set B : List ℕ → Set X := fun t => A (t ++ l₀) with hBdef
      have hBunion : ∀ t, ⋃ c, B (c :: t) = B t := by
        intro t
        have e : (fun c => B (c :: t)) = (fun c => A (c :: (t ++ l₀))) := by
          funext c
          change A ((c :: t) ++ l₀) = A (c :: (t ++ l₀))
          rfl
        rw [e, hAunion]
      have hBmem : y ∈ B [] := by
        change y ∈ A ([] ++ l₀)
        rw [List.nil_append]
        exact hy
      obtain ⟨w, hw⟩ := hroot' B hBunion y hBmem
      set z : ℕ → ℕ := fun j => if j < n then x j else w (j - n) with hzdef
      have hb : ∀ j (hj : j ≤ n),
          PiNat.res (fun j => if j < n then x j else w (j - n)) j =
            PiNat.res x j := by
        intro j
        induction j with
        | zero => intro; rfl
        | succ j IH =>
          intro hj
          have hjN : j < n := Nat.lt_of_succ_le hj
          rw [PiNat.res_succ, PiNat.res_succ, ite_eq_left hjN, IH (Nat.le_of_succ_le hj)]
      have ha : ∀ k, PiNat.res (fun j => if j < n then x j else w (j - n)) (n + k) =
          PiNat.res w k ++ PiNat.res x n := by
        intro k
        induction k with
        | zero =>
          rw [Nat.add_zero, hb n le_rfl, PiNat.res_zero, List.nil_append]
        | succ k IH =>
          have e1 : n + (k + 1) = (n + k) + 1 := by omega
          rw [e1, PiNat.res_succ, PiNat.res_succ]
          have hnk : ¬ n + k < n := by omega
          have ez : (if n + k < n then x (n + k) else w (n + k - n)) = w k := by
            rw [ite_eq_right hnk, Nat.add_sub_cancel_left]
          rw [ez, IH, List.cons_append]
      have hmem_all : ∀ j,
          y ∈ A (PiNat.res (fun j => if j < n then x j else w (j - n)) j) := by
        intro j
        by_cases hj : j ≤ n
        · rw [hb j hj]
          exact hres_sub x j n hj hy
        · push Not at hj
          obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt hj)
          rw [ha k]
          exact hw k
      have hFz : F z = y := by
        apply hfiber z _ y (mem_iInter.mpr (hFmem z))
        exact mem_iInter.mpr hmem_all
      have hzmem : z ∈ PiNat.cylinder x n := by
        have hresN : PiNat.res z n = PiNat.res x n := hb n le_rfl
        intro i hi
        exact (PiNat.res_eq_res.mp hresN) hi
      exact ⟨z, hzmem, hFz⟩
  -- Cylinders form a neighborhood basis.
  have hcyl : ∀ (Vset : Set (ℕ → ℕ)), IsOpen Vset → ∀ x ∈ Vset,
      ∃ n, PiNat.cylinder x n ⊆ Vset := by
    intro Vset hV x hx
    obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hV x hx
    obtain ⟨n, hn⟩ := Finset.exists_nat_subset_range I
    refine ⟨n, fun y hy => hsub ?_⟩
    rw [Set.mem_pi]
    intro a ha
    have han : a < n := Finset.mem_range.mp (hn ha)
    have hay : y a = x a := hy a han
    rw [hay]
    exact (hu a ha).2
  have hFbije : Function.Bijective F := ⟨hFinj, hFsurj⟩
  set e : (ℕ → ℕ) ≃ X := Equiv.ofBijective F hFbije with hedef
  have hpre : ∀ (x : ℕ → ℕ) (n : ℕ),
      e.symm ⁻¹' (PiNat.cylinder x n) = A (PiNat.res x n) := by
    intro x n
    ext y
    constructor
    · intro hy
      have h1 : e.symm y ∈ PiNat.cylinder x n := hy
      have h2 : F (e.symm y) ∈ F '' (PiNat.cylinder x n) :=
        mem_image_of_mem _ h1
      rw [him] at h2
      have h3 : F (e.symm y) = y := e.apply_symm_apply y
      rw [h3] at h2
      exact h2
    · intro hy
      rw [← him] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      have h3 : e.symm (F z) = z := e.symm_apply_apply z
      change e.symm (F z) ∈ PiNat.cylinder x n
      rw [h3]
      exact hz
  have hsymm_cont : Continuous e.symm := by
    rw [continuous_def]
    intro Vset hV
    choose nn hnn using (fun x : ↥Vset => hcyl Vset hV x.val x.property)
    have hself : ∀ (x : ℕ → ℕ) (n : ℕ), x ∈ PiNat.cylinder x n := fun x n i _ => rfl
    have hVeq : Vset = ⋃ x : ↥Vset, PiNat.cylinder x.val (nn x) := by
      apply le_antisymm
      · intro v hv
        apply mem_iUnion.mpr
        refine ⟨⟨v, hv⟩, ?_⟩
        exact hself v _
      · exact iUnion_subset_iff.mpr hnn
    rw [hVeq, preimage_iUnion]
    exact isOpen_iUnion (fun x => by rw [hpre]; exact ((hAgood _).2).isOpen)
  have he_toFun : Continuous e := hFcont
  exact ⟨Homeomorph.mk e.symm hsymm_cont he_toFun⟩

end MathlibExt.Topology.DescriptiveSetTheory.BaireSpaceCharacterizationWanted
