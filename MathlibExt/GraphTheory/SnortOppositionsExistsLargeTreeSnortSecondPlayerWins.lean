/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic

import Mathlib.Tactic.FinCases

/-!
# Arbitrarily large Snort second-player-winning trees

This module defines the bounded Snort outcome, its second-player-win predicate and the
`n`-firework of a graph, and proves the existence of arbitrarily large trees with that outcome:
fireworks of one fixed tree at two hubs.

Source: Rylo Ashmore, Beth Ann Austin, Alfie M. Davies, Danny Dyer, and
William Kellough, "On Graph Automorphisms Related to SNORT", *INTEGERS* 26
(2026), Article G2 (arXiv:2506.20669), Corollary 2 (Corollary 3.6 in arXiv v1).
-/

namespace MetaMathlibExt

@[expose] public section

variable {V W : Type*}

/-- **Snort positions with a move bound.** Let $G$ be a finite simple graph, let $k$ be a natural
number, and let $A$ and $B$ be finite sets of vertices of $G$, the vertices coloured so far by
the player to move and by the opponent. A legal move colours a vertex $v$ that lies in neither
$A$ nor $B$ and has no neighbour in $B$. With move bound $0$ the player to move loses. With move
bound $k + 1$ the player to move wins at $(A, B)$ exactly when some legal move $v$ leaves a
position $(B, A \cup \{v\})$ that the opponent, now to move with move bound $k$, does not win.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1 (rules of
Snort). -/
def snortMoverWins [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    ℕ → Finset V → Finset V → Bool
  | 0, _, _ => false
  | k + 1, mine, theirs =>
      decide (∃ v : V, v ∉ mine ∧ v ∉ theirs ∧ (∀ w ∈ theirs, ¬ G.Adj v w) ∧
        snortMoverWins G k theirs (insert v mine) = false)

/-- **Second-player win in Snort.** Let $G$ be a finite simple graph. In Snort on $G$, two
players alternately colour a vertex of $G$ that is not yet coloured, each with their own
colour, and a player may not colour a vertex adjacent to a vertex of the opponent's colour; a
player with no legal move loses. The second player wins Snort on $G$ if, starting from the
position in which no vertex is coloured, the player who moves first has no winning strategy.

Every move colours a new vertex, so the game ends after at most $|V(G)|$ moves and has no
draws; hence this says that the second player has a winning strategy.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 1. -/
def SnortSecondPlayerWins [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : Prop :=
  snortMoverWins G (Fintype.card V) ∅ ∅ = false

/-- **Firework of a graph.** For a graph $G$, vertices $u$ and $v$ of $G$ and a natural number $n$,
the $n$-firework of $G$ at $(u, v)$ is the graph obtained from $G$ by adding $2n$ new vertices,
$n$ of which are adjacent only to $u$ and the other $n$ adjacent only to $v$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Section 3 (the `n`-firework). -/
def firework (G : SimpleGraph V) (u v : V) (n : ℕ) : SimpleGraph (V ⊕ (Fin n × Bool)) :=
  SimpleGraph.fromRel fun x y => match x, y with
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inl a, Sum.inr (_, false) => a = u
    | Sum.inl a, Sum.inr (_, true) => a = v
    | _, _ => False

private def base : SimpleGraph (Fin 14) :=
  SimpleGraph.fromRel fun u v => (u, v) ∈ ([(0,1),(1,2),(2,3),(0,4),(4,5),(5,6),(6,7),
    (0,8),(8,9),(9,10),(10,11),(3,12),(3,13)] : List (Fin 14 × Fin 14))
private instance : DecidableRel base.Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ _))
private def hub (b : Bool) : Fin 14 := if b then 3 else 0
-- The witness tree: the `m`-firework of `base` at its two hubs `0` and `3`.
local notation "extension " m:max => firework base 0 3 m
private instance (m : ℕ) : DecidableRel (extension m).Adj := by
  intro x y
  cases x with
  | inl a =>
    cases y with
    | inl c => exact inferInstanceAs (Decidable (_ ≠ _ ∧ _))
    | inr p => cases p with | mk i b => cases b <;> exact inferInstanceAs (Decidable (_ ≠ _ ∧ _))
  | inr p =>
    cases p with
    | mk i b =>
      cases y with
      | inl c => cases b <;> exact inferInstanceAs (Decidable (_ ≠ _ ∧ _))
      | inr q => cases b <;> cases q with | mk j d => cases d <;>
          exact inferInstanceAs (Decidable (_ ≠ _ ∧ _))
private def position (m : ℕ) (b : Bool) (A : Finset (Fin 14)) (S : Finset (Fin m)) :
    Finset (Fin 14 ⊕ (Fin m × Bool)) :=
  A.image Sum.inl ∪ S.image (fun i => Sum.inr (i, b))
private theorem losing_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (A B : Finset V) :
    snortMoverWins G (k + 1) A B = false ↔
      ∀ v, v ∉ A → v ∉ B → (∀ w ∈ B, ¬ G.Adj v w) →
        snortMoverWins G k B (insert v A) = true := by
  simp [snortMoverWins]
private theorem winning_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (A B : Finset V) :
    snortMoverWins G (k + 1) A B = true ↔
      ∃ v, v ∉ A ∧ v ∉ B ∧ (∀ w ∈ B, ¬ G.Adj v w) ∧
        snortMoverWins G k B (insert v A) = false := by
  simp [snortMoverWins]
private theorem fuel_stable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) (A B : Finset V)
    (h : Fintype.card V ≤ k + (A ∪ B).card) :
    snortMoverWins G k A B = snortMoverWins G (k + 1) A B := by
  induction k generalizing A B with
  | zero =>
    have hab : A ∪ B = Finset.univ := Finset.eq_of_subset_of_card_le
      (Finset.subset_univ _) (by simpa using h)
    change false = snortMoverWins G 1 A B
    symm
    rw [losing_iff]
    intro v ha hb _
    have hv : v ∈ A ∪ B := hab ▸ Finset.mem_univ v
    simp [ha, hb] at hv
  | succ k ih =>
    rw [snortMoverWins, snortMoverWins]
    congr 1
    apply propext
    constructor <;> rintro ⟨v, ha, hb, hadj, hwin⟩ <;>
      refine ⟨v, ha, hb, hadj, ?_⟩
    · have hc : (B ∪ insert v A).card = (A ∪ B).card + 1 := by
        rw [Finset.union_insert, Finset.union_comm B A, Finset.card_insert_of_notMem]
        simp [ha, hb]
      rw [← ih B (insert v A) (by omega)]
      exact hwin
    · have hc : (B ∪ insert v A).card = (A ∪ B).card + 1 := by
        rw [Finset.union_insert, Finset.union_comm B A, Finset.card_insert_of_notMem]
        simp [ha, hb]
      rw [ih B (insert v A) (by omega)]
      exact hwin
private theorem base_move (m : ℕ) (b : Bool) (A B : Finset (Fin 14))
    (S T : Finset (Fin m)) (v : Fin 14) :
    Sum.inl v ∉ position m b A S ∧ Sum.inl v ∉ position m (!b) B T ∧
      (∀ w ∈ position m (!b) B T, ¬ (extension m).Adj (Sum.inl v) w) ↔
    v ∉ A ∧ v ∉ B ∧
      (∀ w ∈ B, ¬ (extension m).Adj (Sum.inl v) (Sum.inl w)) ∧
      (∀ i ∈ T, ¬ (extension m).Adj (Sum.inl v) (Sum.inr (i, !b))) := by
  simp [position]

private theorem extension_base_adj (m : ℕ) (u v : Fin 14) :
    (extension m).Adj (Sum.inl u) (Sum.inl v) ↔ base.Adj u v := by
  simp only [firework, SimpleGraph.fromRel_adj, ne_eq, Sum.inl.injEq]
  rw [base.adj_comm v u, or_self]
  exact ⟨And.right, fun h => ⟨h.ne, h⟩⟩
private theorem legal_base (m : ℕ) (b : Bool) (A B : Finset (Fin 14))
    (S T : Finset (Fin m)) (hv : hub (!b) ∈ B) (v : Fin 14) :
    Sum.inl v ∉ position m b A S ∧ Sum.inl v ∉ position m (!b) B T ∧
      (∀ w ∈ position m (!b) B T, ¬ (extension m).Adj (Sum.inl v) w) ↔
    v ∉ A ∧ v ∉ B ∧ (∀ w ∈ B, ¬ base.Adj v w) := by
  rw [base_move]
  simp only [extension_base_adj]
  constructor
  · rintro ⟨ha, hb, hadj, _⟩
    exact ⟨ha, hb, hadj⟩
  · rintro ⟨ha, hb, hadj⟩
    refine ⟨ha, hb, hadj, ?_⟩
    have hne : v ≠ hub (!b) := fun h => hb (h ▸ hv)
    intro i _
    cases b <;> simp_all [firework, hub]
private theorem legal_leaf (m : ℕ) (b : Bool) (A B : Finset (Fin 14))
    (S T : Finset (Fin m)) (hu : hub b ∈ A) (hv : hub (!b) ∈ B)
    (hd : Disjoint A B) (i : Fin m) (c : Bool) :
    Sum.inr (i, c) ∉ position m b A S ∧ Sum.inr (i, c) ∉ position m (!b) B T ∧
      (∀ w ∈ position m (!b) B T, ¬ (extension m).Adj (Sum.inr (i, c)) w) ↔
    c = b ∧ i ∉ S := by
  have hnot : hub b ∉ B := fun h => (Finset.disjoint_left.mp hd) hu h
  cases b <;> cases c <;> simp_all [position, firework, hub]
private theorem insert_base (m : ℕ) (b : Bool) (A : Finset (Fin 14))
    (S : Finset (Fin m)) (v : Fin 14) :
    insert (Sum.inl v) (position m b A S) = position m b (insert v A) S := by
  simp [position, Finset.insert_union]
private theorem insert_leaf (m : ℕ) (b : Bool) (A : Finset (Fin 14))
    (S : Finset (Fin m)) (i : Fin m) :
    insert (Sum.inr (i, b)) (position m b A S) = position m b A (insert i S) := by
  simp [position, Finset.union_insert]

private theorem colored_card_insert {V : Type*} [DecidableEq V]
    (A B : Finset V) (v : V) (ha : v ∉ A) (hb : v ∉ B) :
    (B ∪ insert v A).card = (A ∪ B).card + 1 := by
  rw [Finset.union_insert, Finset.union_comm B A, Finset.card_insert_of_notMem]
  simp [ha, hb]
private theorem paired_extension (m : ℕ) (b : Bool) (k : ℕ)
    (A B : Finset (Fin 14)) (S T : Finset (Fin m))
    (hu : hub b ∈ A) (hv : hub (!b) ∈ B) (hd : Disjoint A B)
    (heq : S.card = T.card)
    (hsize : 2 * m + 14 ≤ k + (A ∪ B).card + S.card + T.card)
    (hbase : snortMoverWins base k A B = false) :
    snortMoverWins (extension m) k (position m b A S) (position m (!b) B T) = false := by
  induction k using Nat.strong_induction_on generalizing b A B S T with
  | ind k ih =>
    cases k with
    | zero => rfl
    | succ k =>
      apply (losing_iff (extension m) k _ _).mpr
      intro x hxa hxb hxadj
      cases x with
      | inl v =>
        obtain ⟨ha, hb, hadj⟩ := (legal_base m b A B S T hv v).mp ⟨hxa, hxb, hxadj⟩
        have hnext := (losing_iff base k A B).mp hbase v ha hb hadj
        cases k with
        | zero => simp [snortMoverWins] at hnext
        | succ k =>
          obtain ⟨y, hyb, hya, hyadj, hlose⟩ := (winning_iff base k B (insert v A)).mp hnext
          rw [insert_base]
          apply (winning_iff (extension m) k _ _).mpr
          have hubA : hub (!(!b)) ∈ insert v A := by simpa using Finset.mem_insert_of_mem hu
          have hy := (legal_base m (!b) B (insert v A) T S hubA y).mpr ⟨hyb, hya, hyadj⟩
          simp only [Bool.not_not] at hy
          refine ⟨Sum.inl y, hy.1, hy.2.1, hy.2.2, ?_⟩
          rw [insert_base]
          apply ih k (by omega) b (insert v A) (insert y B) S T
          · exact Finset.mem_insert_of_mem hu
          · exact Finset.mem_insert_of_mem hv
          · simp only [Finset.disjoint_insert_left, Finset.disjoint_insert_right]
            exact ⟨hya, hb, hd⟩
          · exact heq
          · have hc := colored_card_insert A B v ha hb
            have hc' := colored_card_insert B (insert v A) y hyb hya
            omega
          · exact hlose
      | inr p =>
        obtain ⟨i, c⟩ := p
        obtain ⟨hcb, hi⟩ := (legal_leaf m b A B S T hu hv hd i c).mp ⟨hxa, hxb, hxadj⟩
        subst c
        have hs : S.card < m := by
          have hsub : S ⊂ Finset.univ := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
            intro h
            exact hi (h ▸ Finset.mem_univ i)
          simpa using Finset.card_lt_card hsub
        have ht : T.card < m := by omega
        obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
          (show T.card < (Finset.univ : Finset (Fin m)).card by simpa using ht)
        have hc : (A ∪ B).card ≤ 14 := by
          simpa using Finset.card_le_card (Finset.subset_univ (A ∪ B))
        cases k with
        | zero => omega
        | succ k =>
          rw [insert_leaf]
          apply (winning_iff (extension m) k _ _).mpr
          have hubA : hub (!(!b)) ∈ A := by simpa using hu
          have hy := (legal_leaf m (!b) B A T (insert i S) hv hubA hd.symm j (!b)).mpr ⟨rfl, hj⟩
          simp only [Bool.not_not] at hy
          refine ⟨Sum.inr (j, !b), hy.1, hy.2.1, hy.2.2, ?_⟩
          rw [insert_leaf]
          apply ih k (by omega) b A B (insert i S) (insert j T) hu hv hd
          · simp [Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hj, heq]
          · rw [Finset.card_insert_of_notMem hi, Finset.card_insert_of_notMem hj]
            omega
          · have hbound : 14 ≤ k + (A ∪ B).card := by omega
            rw [fuel_stable base k A B (by simpa using hbound),
              fuel_stable base (k + 1) A B
                (by simpa using (show 14 ≤ k + 1 + (A ∪ B).card by omega))]
            exact hbase
private def Legal {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (v : V) : Prop :=
  v ∉ A ∧ v ∉ B ∧ ∀ w ∈ B, ¬ G.Adj v w
private theorem legal_anti {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A B A' B' : Finset V) (ha : A ⊆ A') (hb : B ⊆ B') (v : V)
    (h : Legal G A' B' v) : Legal G A B v :=
  ⟨fun hv => h.1 (ha hv), fun hv => h.2.1 (hb hv), fun w hw => h.2.2 w (hb hw)⟩
private structure ReserveGeometry {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A B C R U : Finset V) : Prop where
  disjointCU : Disjoint C U
  disjointCR : Disjoint C R
  disjointRU : Disjoint R U
  legalR : ∀ r ∈ R, Legal G B A r
  legalU : ∀ u ∈ U, Legal G A B u ∧ Legal G B A u
  forbiddenR : ∀ r ∈ R, ¬ Legal G A B r
  coverage : ∀ v, Legal G A B v → v ∈ C ∪ U
  isolated : ∀ u ∈ R ∪ U, ∀ v, (Legal G A B v ∨ Legal G B A v) → ¬ G.Adj u v
private theorem reserve_step {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A B C R U : Finset V) (h : ReserveGeometry G A B C R U)
    (v w : V) (hv : Legal G A B v) (hw : Legal G B (insert v A) w) :
    ReserveGeometry G (insert v A) (insert w B)
      ((C.erase v).erase w) ((R.erase v).erase w) ((U.erase v).erase w) := by
  have sub (X : Finset V) : (X.erase v).erase w ⊆ X :=
    (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have legal (X : Finset V) (hl : ∀ x ∈ X, Legal G A B x ∧ Legal G B A x)
      (hX : X ⊆ R ∪ U) (x : V) (hx : x ∈ (X.erase v).erase w) :
      Legal G (insert v A) (insert w B) x ∧ Legal G (insert w B) (insert v A) x := by
    obtain ⟨hxw, hxv, hxX⟩ := (by simpa only [Finset.mem_erase] using hx : x ≠ w ∧ x ≠ v ∧ x ∈ X)
    obtain ⟨hleft, hright⟩ := hl x hxX
    have hxv' := h.isolated x (hX hxX) v (Or.inl hv)
    have hxw' := h.isolated x (hX hxX) w
      (Or.inr (legal_anti G B A B (insert v A) (by rfl) (Finset.subset_insert _ _) w hw))
    constructor <;> constructor
    · simpa using And.intro hxv hleft.1
    · exact ⟨by simpa using And.intro hxw hleft.2.1, by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hxw'
        · exact hleft.2.2 y hy⟩
    · simpa using And.intro hxw hright.1
    · exact ⟨by simpa using And.intro hxv hright.2.1, by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hxv'
        · exact hright.2.2 y hy⟩
  refine ⟨h.disjointCU.mono (sub C) (sub U), h.disjointCR.mono (sub C) (sub R),
    h.disjointRU.mono (sub R) (sub U), ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨hrw, hrv, hrR⟩ := (by simpa only [Finset.mem_erase] using hr : r ≠ w ∧ r ≠ v ∧ r ∈ R)
    obtain ⟨hra, hrb, hrAdj⟩ := h.legalR r hrR
    refine ⟨by simpa using And.intro hrw hra, by simpa using And.intro hrv hrb, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with hy | hy
    · subst y
      exact h.isolated r (Finset.mem_union_left _ hrR) v (Or.inl hv)
    · exact hrAdj y hy
  · exact legal U h.legalU (Finset.subset_union_right)
  · intro r hr hlegal
    exact h.forbiddenR r (sub R hr) (legal_anti G A B _ _
      (Finset.subset_insert _ _) (Finset.subset_insert _ _) r hlegal)
  · intro x hx
    have old := legal_anti G A B _ _ (Finset.subset_insert _ _) (Finset.subset_insert _ _) x hx
    have hxv : x ≠ v := fun he => hx.1 (he ▸ Finset.mem_insert_self _ _)
    have hxw : x ≠ w := fun he => hx.2.1 (he ▸ Finset.mem_insert_self _ _)
    apply Finset.mem_union.mpr
    rcases Finset.mem_union.mp (h.coverage x old) with hxC | hxU
    · exact Or.inl (Finset.mem_erase.mpr ⟨hxw, Finset.mem_erase.mpr ⟨hxv, hxC⟩⟩)
    · exact Or.inr (Finset.mem_erase.mpr ⟨hxw, Finset.mem_erase.mpr ⟨hxv, hxU⟩⟩)
  · intro x hx y hy
    have hxold : x ∈ R ∪ U := Finset.mem_union.mpr <| by
      rcases Finset.mem_union.mp hx with hr | hu
      · exact Or.inl (sub R hr)
      · exact Or.inr (sub U hu)
    apply h.isolated x hxold y
    rcases hy with hy | hy
    · exact Or.inl (legal_anti G A B _ _ (Finset.subset_insert _ _) (Finset.subset_insert _ _) y hy)
    · exact Or.inr (legal_anti G B A _ _ (Finset.subset_insert _ _) (Finset.subset_insert _ _) y hy)
private theorem legal_after {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (v w : V) (hw : Legal G B A w) (hne : w ≠ v)
    (hadj : ¬ G.Adj w v) : Legal G B (insert v A) w := by
  refine ⟨hw.1, by simpa using And.intro hne hw.2.1, ?_⟩
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hadj
  · exact hw.2.2 x hx
private theorem reservoir_loses {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) (A B C R U : Finset V)
    (h : ReserveGeometry G A B C R U) (hcard : C.card + U.card % 2 ≤ R.card) :
    snortMoverWins G (2 * t) A B = false := by
  induction t generalizing A B C R U with
  | zero => rfl
  | succ t ih =>
    rw [Nat.mul_succ]
    apply (losing_iff G (2 * t + 1) A B).mpr
    intro v hva hvb hvadj
    have hv : Legal G A B v := ⟨hva, hvb, hvadj⟩
    apply (winning_iff G (2 * t) B (insert v A)).mpr
    rcases Finset.mem_union.mp (h.coverage v hv) with hvC | hvU
    · have hvR : v ∉ R := fun hr => Finset.disjoint_left.mp h.disjointCR hvC hr
      have hvU : v ∉ U := fun hu => Finset.disjoint_left.mp h.disjointCU hvC hu
      have hC : 0 < C.card := Finset.card_pos.mpr ⟨v, hvC⟩
      have hR : 0 < R.card := by omega
      obtain ⟨w, hwR⟩ := Finset.card_pos.mp hR
      have hwC : w ∉ C := fun hc => Finset.disjoint_left.mp h.disjointCR hc hwR
      have hwU : w ∉ U := fun hu => Finset.disjoint_left.mp h.disjointRU hwR hu
      have hne : w ≠ v := fun he => hvR (he ▸ hwR)
      have hw := legal_after G A B v w (h.legalR w hwR) hne
        (h.isolated w (Finset.mem_union_left _ hwR) v (Or.inl hv))
      refine ⟨w, hw.1, hw.2.1, hw.2.2, ?_⟩
      apply ih (insert v A) (insert w B) ((C.erase v).erase w)
        ((R.erase v).erase w) ((U.erase v).erase w) (reserve_step G A B C R U h v w hv hw)
      have hwC' : w ∉ C.erase v := fun hc => hwC (Finset.mem_of_mem_erase hc)
      simp only [Finset.erase_eq_of_notMem hwC', Finset.erase_eq_of_notMem hvR,
        Finset.erase_eq_of_notMem hvU, Finset.erase_eq_of_notMem hwU,
        Finset.card_erase_of_mem hvC, Finset.card_erase_of_mem hwR]
      omega
    · have hvC : v ∉ C := fun hc => Finset.disjoint_left.mp h.disjointCU hc hvU
      have hvR : v ∉ R := fun hr => Finset.disjoint_left.mp h.disjointRU hr hvU
      by_cases hex : (U.erase v).Nonempty
      · obtain ⟨w, hw⟩ := hex
        obtain ⟨hnev, hwU⟩ := Finset.mem_erase.mp hw
        have hwC : w ∉ C := fun hc => Finset.disjoint_left.mp h.disjointCU hc hwU
        have hwR : w ∉ R := fun hr => Finset.disjoint_left.mp h.disjointRU hr hwU
        have hwlegal := legal_after G A B v w (h.legalU w hwU).2 hnev
          (h.isolated w (Finset.mem_union_right _ hwU) v (Or.inl hv))
        refine ⟨w, hwlegal.1, hwlegal.2.1, hwlegal.2.2, ?_⟩
        apply ih (insert v A) (insert w B) ((C.erase v).erase w)
          ((R.erase v).erase w) ((U.erase v).erase w)
          (reserve_step G A B C R U h v w hv hwlegal)
        have he : (U.erase v).card + 1 = U.card := Finset.card_erase_add_one hvU
        have he' : 0 < (U.erase v).card := Finset.card_pos.mpr ⟨w, hw⟩
        simp only [Finset.erase_eq_of_notMem hvC, Finset.erase_eq_of_notMem hwC,
          Finset.erase_eq_of_notMem hvR, Finset.erase_eq_of_notMem hwR,
          Finset.card_erase_of_mem hw, Finset.card_erase_of_mem hvU]
        omega
      · have hempty : U.erase v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hex
        have hU : U.card = 1 := by
          have he := Finset.card_erase_add_one hvU
          simpa [hempty] using he.symm
        have hR : 0 < R.card := by omega
        obtain ⟨w, hwR⟩ := Finset.card_pos.mp hR
        have hwC : w ∉ C := fun hc => Finset.disjoint_left.mp h.disjointCR hc hwR
        have hne : w ≠ v := fun he => hvR (he ▸ hwR)
        have hw := legal_after G A B v w (h.legalR w hwR) hne
          (h.isolated w (Finset.mem_union_left _ hwR) v (Or.inl hv))
        refine ⟨w, hw.1, hw.2.1, hw.2.2, ?_⟩
        apply ih (insert v A) (insert w B) ((C.erase v).erase w)
          ((R.erase v).erase w) ((U.erase v).erase w) (reserve_step G A B C R U h v w hv hw)
        simp only [Finset.erase_eq_of_notMem hvC, Finset.erase_eq_of_notMem hwC,
          Finset.erase_eq_of_notMem hvR, hempty, Finset.erase_empty, Finset.card_empty,
          Nat.zero_mod, Nat.add_zero, Finset.card_erase_of_mem hwR]
        omega

private theorem extension_leaf_adj (m : ℕ) (i : Fin m) (b : Bool)
    (x : Fin 14 ⊕ (Fin m × Bool)) :
    (extension m).Adj (Sum.inr (i, b)) x ↔ x = Sum.inl (hub b) := by
  cases x <;> cases b <;> simp [firework, hub, eq_comm]
private theorem legal_leaf_any (m : ℕ) (b : Bool) (A B : Finset (Fin 14 ⊕ (Fin m × Bool)))
    (i : Fin m) :
    Legal (extension m) A B (Sum.inr (i, b)) ↔
      Sum.inr (i, b) ∉ A ∧ Sum.inr (i, b) ∉ B ∧ Sum.inl (hub b) ∉ B := by
  simp [Legal, extension_leaf_adj]
private theorem reserve_from_hubs (m : ℕ) (hm : 15 ≤ m) (b : Bool) (t : ℕ)
    (A B : Finset (Fin 14 ⊕ (Fin m × Bool))) (hd : Disjoint A B)
    (hv : Sum.inl (hub b) ∈ B)
    (hfresh : ∀ i, Sum.inr (i, b) ∉ A ∧ Sum.inr (i, b) ∉ B)
    (hu : Sum.inl (hub (!b)) ∈ B ∨
      (Sum.inl (hub (!b)) ∉ A ∧ Sum.inl (hub (!b)) ∉ B ∧
        ¬ Legal (extension m) A B (Sum.inl (hub (!b))) ∧
        ¬ Legal (extension m) B A (Sum.inl (hub (!b))))) :
    snortMoverWins (extension m) (2 * t) A B = false := by
  let C := (Finset.univ.image (Sum.inl : Fin 14 → Fin 14 ⊕ (Fin m × Bool))) \ (A ∪ B)
  let R : Finset (Fin 14 ⊕ (Fin m × Bool)) := Finset.univ.image (fun i : Fin m => Sum.inr (i, b))
  let U : Finset (Fin 14 ⊕ (Fin m × Bool)) := if Sum.inl (hub (!b)) ∈ B then ∅ else
    (Finset.univ.image (fun i : Fin m => Sum.inr (i, !b))) \ (A ∪ B)
  have memC (x) : x ∈ C ↔ x ∉ A ∧ x ∉ B ∧ ∃ v, x = Sum.inl v := by
    simp [C, and_comm, and_assoc, eq_comm]
  have memR (x) : x ∈ R ↔ ∃ i, x = Sum.inr (i, b) := by simp [R, eq_comm]
  have memU (x) : x ∈ U ↔ Sum.inl (hub (!b)) ∉ B ∧ x ∉ A ∧ x ∉ B ∧
      ∃ i, x = Sum.inr (i, !b) := by
    by_cases h : Sum.inl (hub (!b)) ∈ B <;> simp [U, h, and_comm, and_assoc, eq_comm]
  have hbnot : Sum.inl (hub b) ∉ A := fun h => Finset.disjoint_left.mp hd h hv
  have hbplay : ¬ Legal (extension m) A B (Sum.inl (hub b)) ∧
      ¬ Legal (extension m) B A (Sum.inl (hub b)) :=
    ⟨fun h => h.2.1 hv, fun h => h.1 hv⟩
  have huplay : ¬ Legal (extension m) A B (Sum.inl (hub (!b))) ∧
      ¬ Legal (extension m) B A (Sum.inl (hub (!b))) := by
    rcases hu with hu | ⟨_, _, hleft, hright⟩
    · exact ⟨fun h => h.2.1 hu, fun h => h.1 hu⟩
    · exact ⟨hleft, hright⟩
  have hgeom : ReserveGeometry (extension m) A B C R U := by
    constructor
    · rw [Finset.disjoint_left]
      intro x hxC hxU
      obtain ⟨_, _, v, rfl⟩ := (memC x).mp hxC
      obtain ⟨_, _, _, i, hi⟩ := (memU _).mp hxU
      cases hi
    · rw [Finset.disjoint_left]
      intro x hxC hxR
      obtain ⟨_, _, v, rfl⟩ := (memC x).mp hxC
      obtain ⟨i, hi⟩ := (memR _).mp hxR
      cases hi
    · rw [Finset.disjoint_left]
      intro x hxR hxU
      obtain ⟨i, rfl⟩ := (memR x).mp hxR
      obtain ⟨_, _, _, j, hj⟩ := (memU _).mp hxU
      have hh : b = !b := congrArg Prod.snd (Sum.inr.inj hj)
      cases b <;> contradiction
    · intro x hx
      obtain ⟨i, rfl⟩ := (memR x).mp hx
      exact (legal_leaf_any m b B A i).mpr ⟨(hfresh i).2, (hfresh i).1, hbnot⟩
    · intro x hx
      obtain ⟨hnB, hxA, hxB, i, rfl⟩ := (memU x).mp hx
      have hnA : Sum.inl (hub (!b)) ∉ A := by
        rcases hu with hu | ⟨hnA, _, _, _⟩
        · exact False.elim (hnB hu)
        · exact hnA
      exact ⟨(legal_leaf_any m (!b) A B i).mpr ⟨hxA, hxB, hnB⟩,
        (legal_leaf_any m (!b) B A i).mpr ⟨hxB, hxA, hnA⟩⟩
    · intro x hx hlegal
      obtain ⟨i, rfl⟩ := (memR x).mp hx
      exact ((legal_leaf_any m b A B i).mp hlegal).2.2 hv
    · intro x hx
      cases x with
      | inl v => exact Finset.mem_union_left _ ((memC _).mpr ⟨hx.1, hx.2.1, v, rfl⟩)
      | inr p =>
        obtain ⟨i, c⟩ := p
        by_cases hcb : c = b
        · subst c
          exact False.elim (((legal_leaf_any m b A B i).mp hx).2.2 hv)
        · have hc : c = !b := by cases b <;> cases c <;> simp_all
          subst c
          have hnB := ((legal_leaf_any m (!b) A B i).mp hx).2.2
          exact Finset.mem_union_right _ ((memU _).mpr ⟨hnB, hx.1, hx.2.1, i, rfl⟩)
    · intro x hx y hy
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨i, rfl⟩ := (memR x).mp hx
        rw [extension_leaf_adj]
        rintro rfl
        exact hy.elim hbplay.1 hbplay.2
      · obtain ⟨_, _, _, i, rfl⟩ := (memU x).mp hx
        rw [extension_leaf_adj]
        rintro rfl
        exact hy.elim huplay.1 huplay.2
  have hC : C.card ≤ 14 := by
    calc
      C.card ≤ (Finset.univ.image (Sum.inl : Fin 14 → Fin 14 ⊕ (Fin m × Bool))).card :=
        Finset.card_le_card Finset.sdiff_subset
      _ = 14 := by simp [Finset.card_image_of_injective _ Sum.inl_injective]
  have hR : R.card = m := by
    have hinj : Function.Injective (fun i : Fin m => (Sum.inr (i, b) : Fin 14 ⊕ (Fin m × Bool))) :=
      fun i j h => congrArg Prod.fst (Sum.inr.inj h)
    simp [R, Finset.card_image_of_injective _ hinj]
  apply reservoir_loses (extension m) t A B C R U hgeom
  omega
private theorem fuel_ge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k l : ℕ) (A B : Finset V)
    (hbound : Fintype.card V ≤ k + (A ∪ B).card) (hkl : k ≤ l) :
    snortMoverWins G l A B = snortMoverWins G k A B := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkl
  clear hkl
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ, ← fuel_stable G (k + n) A B (by omega)]
    exact ih
private theorem paired_outcome (m : ℕ) (b : Bool) (k : ℕ)
    (A B : Finset (Fin 14)) (S T : Finset (Fin m))
    (hu : hub b ∈ A) (hv : hub (!b) ∈ B) (hd : Disjoint A B)
    (heq : S.card = T.card)
    (hsize : 2 * m + 14 ≤ k + (A ∪ B).card + S.card + T.card) :
    snortMoverWins (extension m) k (position m b A S) (position m (!b) B T) =
      snortMoverWins base k A B := by
  cases hbase : snortMoverWins base k A B with
  | false => exact paired_extension m b k A B S T hu hv hd heq hsize hbase
  | true =>
    cases k with
    | zero => simp [snortMoverWins] at hbase
    | succ k =>
      obtain ⟨v, ha, hb, hadj, hlose⟩ := (winning_iff base k A B).mp hbase
      have hlegal := (legal_base m b A B S T hv v).mpr ⟨ha, hb, hadj⟩
      apply (winning_iff (extension m) k _ _).mpr
      refine ⟨Sum.inl v, hlegal.1, hlegal.2.1, hlegal.2.2, ?_⟩
      rw [insert_base]
      have hubA : hub (!(!b)) ∈ insert v A := by simpa using Finset.mem_insert_of_mem hu
      simpa only [Bool.not_not] using paired_extension m (!b) k B (insert v A) T S hv hubA
        (by simp [Finset.disjoint_insert_right, hb, hd.symm]) heq.symm
        (by have hc := colored_card_insert A B v ha hb; omega) hlose
private theorem base_pair (b : Bool) :
    snortMoverWins base 12 {hub b} {hub (!b)} = false := by
  cases b <;> decide +kernel
@[simp] private theorem hubs_ne (b : Bool) : hub b ≠ hub (!b) := by cases b <;> decide
@[simp] private theorem hubs_ne_reverse (b : Bool) : hub (!b) ≠ hub b := (hubs_ne b).symm
private theorem extension_pair (m : ℕ) (b : Bool) :
    snortMoverWins (extension m) (2 * m + 12) {Sum.inl (hub b)} {Sum.inl (hub (!b))} = false := by
  have hbase : snortMoverWins base (2 * m + 12) {hub b} {hub (!b)} = false := by
    rw [fuel_ge base 12 (2 * m + 12) {hub b} {hub (!b)} (by simp) (by omega)]
    exact base_pair b
  simpa [position] using paired_extension m b (2 * m + 12) {hub b} {hub (!b)} ∅ ∅
    (by simp) (by simp) (by simp) (by simp)
    (by simp) hbase

private theorem after_other_hub (m : ℕ) (hm : 15 ≤ m) (b : Bool)
    (x : Fin 14 ⊕ (Fin m × Bool))
    (hreply : Legal (extension m) ∅ {x} (Sum.inl (hub b)))
    (hne : x ≠ Sum.inl (hub (!b))) :
    snortMoverWins (extension m) (2 * m + 11) {Sum.inl (hub b)}
      (insert (Sum.inl (hub (!b))) {x}) = true := by
  have hxv : x ≠ Sum.inl (hub b) := by
    intro he
    exact hreply.2.1 (by simp [he])
  have hxadj : ¬ (extension m).Adj x (Sum.inl (hub b)) :=
    fun h => hreply.2.2 x (by simp) h.symm
  cases x with
  | inl a =>
    have ha : a ≠ hub (!b) := by simpa only [ne_eq, Sum.inl.injEq] using hne
    have ha' : a ≠ hub b := by simpa only [ne_eq, Sum.inl.injEq] using hxv
    have hadj : ¬ base.Adj a (hub b) := fun h => hxadj ((extension_base_adj m _ _).mpr h)
    have hbase : snortMoverWins base 11 {hub b} (insert a {hub (!b)}) = true := by
      have hpair := base_pair (!b)
      simp only [Bool.not_not] at hpair
      exact (losing_iff base 11 _ _).mp hpair a (by simp [ha]) (by simp [ha'])
        (by simpa using hadj)
    have hbound : 14 ≤ 11 + ({hub b} ∪ insert a {hub (!b)} : Finset (Fin 14)).card := by
      simp [ha, ha', Finset.union_insert]
    have hbase' : snortMoverWins base (2 * m + 11) {hub b} (insert a {hub (!b)}) = true := by
      rw [fuel_ge base 11 (2 * m + 11) _ _ (by simpa using hbound) (by omega)]
      exact hbase
    have hout := paired_outcome m b (2 * m + 11) {hub b} (insert a {hub (!b)}) ∅ ∅
      (by simp) (by simp) (by simp [ha'.symm])
      (by simp) (by simp only [Finset.card_empty, Nat.add_zero]; omega)
    simpa [position, Finset.pair_comm] using hout.trans hbase'
  | inr p =>
    obtain ⟨i, c⟩ := p
    have hc : c = !b := by cases b <;> cases c <;> simp_all [extension_leaf_adj, hub]
    subst c
    let j : Fin m := ⟨0, by omega⟩
    apply (winning_iff (extension m) (2 * m + 10) _ _).mpr
    have hlegal : Legal (extension m) {Sum.inl (hub b)}
        (insert (Sum.inl (hub (!b))) {Sum.inr (i, !b)}) (Sum.inr (j, b)) := by
      rw [legal_leaf_any]
      simp
    refine ⟨Sum.inr (j, b), hlegal.1, hlegal.2.1, hlegal.2.2, ?_⟩
    have hbase : snortMoverWins base (2 * m + 10) {hub (!b)} {hub b} = false := by
      rw [fuel_ge base 12 (2 * m + 10) _ _ (by simp) (by omega)]
      simpa using base_pair (!b)
    have hout := paired_extension m (!b) (2 * m + 10) {hub (!b)} {hub b} {i} {j}
      (by simp) (by simp) (by simp)
      (by simp) (by simp) hbase
    simpa [position, Finset.pair_comm] using hout

private theorem disjoint_insert_mine {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hd : Disjoint A B) (v : V) (hv : Legal G A B v) :
    Disjoint (insert v A) B := by simp [Finset.disjoint_insert_left, hv.2.1, hd]
private theorem fresh_chosen_leaves (m : ℕ) (b : Bool)
    (x y : Fin 14 ⊕ (Fin m × Bool))
    (hx : Legal (extension m) ∅ {x} (Sum.inl (hub b)))
    (hy : Legal (extension m) {x} {Sum.inl (hub b)} y) :
    ∀ i : Fin m, Sum.inr (i, b) ∉ (insert y {x} : Finset (Fin 14 ⊕ (Fin m × Bool))) := by
  intro i
  have hix : Sum.inr (i, b) ≠ x := by
    intro he
    exact hx.2.2 x (by simp) (he ▸ ((extension_leaf_adj m i b _).mpr rfl).symm)
  have hiy : Sum.inr (i, b) ≠ y := by
    intro he
    exact hy.2.2 (Sum.inl (hub b)) (by simp) (he ▸ (extension_leaf_adj m i b _).mpr rfl)
  simpa using And.intro hiy hix
private theorem loses_after_reply (m : ℕ) (hm : 15 ≤ m) (b : Bool)
    (x : Fin 14 ⊕ (Fin m × Bool))
    (hx : Legal (extension m) ∅ {x} (Sum.inl (hub b))) :
    snortMoverWins (extension m) (2 * m + 12) {x} {Sum.inl (hub b)} = false := by
  by_cases hxu : x = Sum.inl (hub (!b))
  · subst x
    simpa using extension_pair m (!b)
  · apply (losing_iff (extension m) (2 * m + 11) _ _).mpr
    intro y hya hyb hyadj
    have hy : Legal (extension m) {x} {Sum.inl (hub b)} y := ⟨hya, hyb, hyadj⟩
    by_cases hyu : y = Sum.inl (hub (!b))
    · subst y
      exact after_other_hub m hm b x hx hxu
    · apply (winning_iff (extension m) (2 * m + 10) _ _).mpr
      have hxv : x ≠ Sum.inl (hub b) := by
        intro he
        exact hx.2.1 (by simp [he])
      have hd : Disjoint (insert y {x}) {Sum.inl (hub b)} :=
        disjoint_insert_mine (extension m) {x} _ (by simp [hxv]) y hy
      have hfresh := fresh_chosen_leaves m b x y hx hy
      have hnotA : Sum.inl (hub (!b)) ∉ (insert y {x} : Finset (Fin 14 ⊕ (Fin m × Bool))) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun h => hyu h.symm, fun h => hxu h.symm⟩
      have hnotB : Sum.inl (hub (!b)) ∉ ({Sum.inl (hub b)} : Finset (Fin 14 ⊕ (Fin m × Bool))) := by
        simp
      by_cases hlegal : Legal (extension m) {Sum.inl (hub b)} (insert y {x}) (Sum.inl (hub (!b)))
      · refine ⟨Sum.inl (hub (!b)), hlegal.1, hlegal.2.1, hlegal.2.2, ?_⟩
        have hd' := (disjoint_insert_mine (extension m) _ _ hd.symm _ hlegal).symm
        have h := reserve_from_hubs m hm b (5 + m) (insert y {x})
          (insert (Sum.inl (hub (!b))) {Sum.inl (hub b)}) hd' (by simp)
          (fun i => ⟨hfresh i, by simp⟩) (Or.inl (by simp))
        have hfuel : 2 * (5 + m) = 2 * m + 10 := by omega
        simpa only [hfuel] using h
      · let P : Finset (Fin 14 ⊕ (Fin m × Bool)) :=
          Finset.univ.image (fun i : Fin m => Sum.inr (i, !b))
        have hP : P.card = m := by
          have hinj : Function.Injective
              (fun i : Fin m => (Sum.inr (i, !b) : Fin 14 ⊕ (Fin m × Bool))) :=
            fun i j h => congrArg Prod.fst (Sum.inr.inj h)
          simp [P, Finset.card_image_of_injective _ hinj]
        have hA : (insert y {x} : Finset (Fin 14 ⊕ (Fin m × Bool))).card ≤ 2 := by
          simpa using Finset.card_insert_le y {x}
        obtain ⟨w, hwP, hwA⟩ := Finset.exists_mem_notMem_of_card_lt_card
          (show (insert y {x} : Finset (Fin 14 ⊕ (Fin m × Bool))).card < P.card by omega)
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hwP
        have hw : Legal (extension m) {Sum.inl (hub b)} (insert y {x}) (Sum.inr (i, !b)) :=
          (legal_leaf_any m (!b) _ _ i).mpr ⟨by simp, hwA, hnotA⟩
        refine ⟨Sum.inr (i, !b), hw.1, hw.2.1, hw.2.2, ?_⟩
        have hd' := (disjoint_insert_mine (extension m) _ _ hd.symm _ hw).symm
        let B' : Finset (Fin 14 ⊕ (Fin m × Bool)) := insert (Sum.inr (i, !b)) {Sum.inl (hub b)}
        have hu : Sum.inl (hub (!b)) ∈ B' ∨
            (Sum.inl (hub (!b)) ∉ (insert y {x} : Finset (Fin 14 ⊕ (Fin m × Bool))) ∧
              Sum.inl (hub (!b)) ∉ B' ∧
              ¬ Legal (extension m) (insert y {x})
                (B') (Sum.inl (hub (!b))) ∧
              ¬ Legal (extension m) (B')
                (insert y {x}) (Sum.inl (hub (!b)))) := by
          refine Or.inr ⟨hnotA, by simp [B'], ?_, ?_⟩
          · intro h
            exact h.2.2 (Sum.inr (i, !b)) (by simp [B'])
              ((extension_leaf_adj m i (!b) _).mpr rfl).symm
          · intro h
            exact hlegal (legal_anti (extension m) _ _ _ _ (Finset.subset_insert _ _)
              (by rfl) _ h)
        have hfresh' : ∀ j, Sum.inr (j, b) ∉ (insert y {x} : Finset (Fin 14 ⊕ (Fin m × Bool))) ∧
            Sum.inr (j, b) ∉ B' := by
          intro j
          exact ⟨hfresh j, by cases b <;> simp [B']⟩
        have h := reserve_from_hubs m hm b (5 + m) (insert y {x})
          (B') hd' (by simp [B']) hfresh' hu
        have hfuel : 2 * (5 + m) = 2 * m + 10 := by omega
        simpa only [hfuel] using h
private theorem hub_reply (m : ℕ) (x : Fin 14 ⊕ (Fin m × Bool)) :
    ∃ b, Legal (extension m) ∅ {x} (Sum.inl (hub b)) := by
  cases x with
  | inl a =>
    have h : ∀ a : Fin 14, ∃ b, hub b ≠ a ∧ ¬ base.Adj (hub b) a := by decide +kernel
    obtain ⟨b, hne, hadj⟩ := h a
    exact ⟨b, by simpa [Legal, extension_base_adj] using And.intro hne hadj⟩
  | inr p =>
    obtain ⟨i, c⟩ := p
    refine ⟨!c, ?_⟩
    cases c <;> simp [Legal, firework, hub]
private theorem extension_second (m : ℕ) (hm : 15 ≤ m) : SnortSecondPlayerWins (extension m) := by
  unfold SnortSecondPlayerWins
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool]
  rw [Nat.mul_comm m 2, Nat.add_comm 14 (2 * m)]
  apply (losing_iff (extension m) (2 * m + 13) _ _).mpr
  intro x _ _ _
  obtain ⟨b, hb⟩ := hub_reply m x
  apply (winning_iff (extension m) (2 * m + 12) _ _).mpr
  exact ⟨Sum.inl (hub b), hb.1, hb.2.1, hb.2.2, loses_after_reply m hm b x hb⟩

private theorem base_tree : base.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨0, ?_⟩
    have h01 : base.Adj 0 1 := by decide
    have h12 : base.Adj 1 2 := by decide
    have h23 : base.Adj 2 3 := by decide
    have h04 : base.Adj 0 4 := by decide
    have h45 : base.Adj 4 5 := by decide
    have h56 : base.Adj 5 6 := by decide
    have h67 : base.Adj 6 7 := by decide
    have h08 : base.Adj 0 8 := by decide
    have h89 : base.Adj 8 9 := by decide
    have h910 : base.Adj 9 10 := by decide
    have h1011 : base.Adj 10 11 := by decide
    have h312 : base.Adj 3 12 := by decide
    have h313 : base.Adj 3 13 := by decide
    intro v
    fin_cases v
    · exact SimpleGraph.Reachable.refl 0
    · exact h01.reachable
    · exact h01.reachable.trans h12.reachable
    · exact (h01.reachable.trans h12.reachable).trans h23.reachable
    · exact h04.reachable
    · exact h04.reachable.trans h45.reachable
    · exact (h04.reachable.trans h45.reachable).trans h56.reachable
    · exact ((h04.reachable.trans h45.reachable).trans h56.reachable).trans h67.reachable
    · exact h08.reachable
    · exact h08.reachable.trans h89.reachable
    · exact (h08.reachable.trans h89.reachable).trans h910.reachable
    · exact ((h08.reachable.trans h89.reachable).trans h910.reachable).trans h1011.reachable
    · exact (((h01.reachable.trans h12.reachable).trans h23.reachable).trans h312.reachable)
    · exact (((h01.reachable.trans h12.reachable).trans h23.reachable).trans h313.reachable)
  · rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
    decide

private theorem extension_tree (m : ℕ) : (extension m).IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  constructor
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨Sum.inl 0, ?_⟩
    let f : base →g extension m := ⟨Sum.inl, fun {u v} h => (extension_base_adj m u v).mpr h⟩
    intro x
    cases x with
    | inl a => exact (base_tree.connected 0 a).map f
    | inr p =>
      have h : (extension m).Adj (Sum.inr p) (Sum.inl (hub p.2)) :=
        (extension_leaf_adj m p.1 p.2 _).mpr rfl
      exact ((base_tree.connected 0 (hub p.2)).map f).trans h.symm.reachable
  · let E := base.edgeFinset.image (Sym2.map (Sum.inl : Fin 14 → Fin 14 ⊕ (Fin m × Bool)))
    let L := (Finset.univ : Finset (Fin m × Bool)).image (fun p => s(Sum.inl (hub p.2), Sum.inr p))
    have hedges : (extension m).edgeFinset = E ∪ L := by
      ext e
      induction e using Sym2.inductionOn with
      | hf x y =>
        simp only [E, L, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
        simp only [Sym2.exists, SimpleGraph.mem_edgeSet,
          Sym2.map_mk, Sym2.eq_iff]
        cases x with
        | inl a =>
          cases y with
          | inl b =>
            simp only [extension_base_adj, Sum.inl.injEq, Sum.inr_ne_inl,
              and_false, or_false, exists_false]
            constructor
            · intro h
              exact ⟨a, b, h, Or.inl ⟨rfl, rfl⟩⟩
            · rintro ⟨u, v, h, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
              · exact h
              · exact h.symm
          | inr p =>
            rw [(extension m).adj_comm]
            obtain ⟨i, c⟩ := p
            simp [extension_leaf_adj, and_comm, eq_comm]
        | inr p =>
          obtain ⟨i, c⟩ := p
          cases y <;> simp [extension_leaf_adj, and_comm, eq_comm]
    have hdisj : Disjoint E L := by
      rw [Finset.disjoint_left]
      intro e he hl
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hl
      induction q using Sym2.inductionOn with
      | hf a b =>
        have h := Sym2.eq_iff.mp hp
        rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h
    have hiL : Function.Injective
        (fun p : Fin m × Bool => s(Sum.inl (hub p.2), (Sum.inr p : Fin 14 ⊕ (Fin m × Bool)))) := by
      intro p q hpq
      rcases Sym2.eq_iff.mp hpq with ⟨_, h⟩ | ⟨h, _⟩
      · exact Sum.inr.inj h
      · cases h
    have hbasecard : base.edgeFinset.card = 13 := by decide
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card, hedges,
      Finset.card_union_of_disjoint hdisj, Nat.card_eq_fintype_card]
    simp [E, L, Finset.card_image_of_injective _ (Sym2.map.injective Sum.inl_injective),
      Finset.card_image_of_injective _ hiL, hbasecard]
    omega

private theorem snort_iso {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (e : G ≃g H) (k : ℕ) (A B : Finset V) :
    snortMoverWins H k (A.image e) (B.image e) = snortMoverWins G k A B := by
  induction k generalizing A B with
  | zero => rfl
  | succ k ih =>
    rw [snortMoverWins, snortMoverWins]
    congr 1
    apply propext
    constructor
    · rintro ⟨v, ha, hb, hadj, hlose⟩
      obtain ⟨u, rfl⟩ := e.surjective v
      refine ⟨u, by simpa [e.injective.eq_iff] using ha,
        by simpa [e.injective.eq_iff] using hb, ?_, ?_⟩
      · intro w hw h
        exact hadj (e w) (Finset.mem_image_of_mem _ hw) (e.map_adj_iff.mpr h)
      · rw [← Finset.image_insert, ih] at hlose
        exact hlose
    · rintro ⟨u, ha, hb, hadj, hlose⟩
      refine ⟨e u, by simpa [e.injective.eq_iff] using ha,
        by simpa [e.injective.eq_iff] using hb, ?_, ?_⟩
      · intro w hw h
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
        exact hadj v hv (e.map_adj_iff.mp h)
      · rw [← Finset.image_insert, ih]
        exact hlose

/-- **Arbitrarily large trees on which the second player wins Snort.** For every natural number
$N$ there is a tree $T$ on $n \ge N$ vertices such that the second player wins Snort on $T$.

Source: Ashmore, Austin, Davies, Dyer, Kellough, *On Graph Automorphisms
Related to SNORT*, INTEGERS 26 (2026), Article G2, Corollary 2. -/
public theorem exists_large_tree_snortSecondPlayerWins (N : ℕ) :
    ∃ n ≥ N, ∃ T : SimpleGraph (Fin n), ∃ _ : DecidableRel T.Adj,
      T.IsTree ∧ SnortSecondPlayerWins T
    := by
  classical
  let m := N + 15
  let n := 2 * m + 14
  have hc : Fintype.card (Fin 14 ⊕ (Fin m × Bool)) = n := by
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_prod, Fintype.card_bool]
    dsimp [n]
    omega
  let T := (extension m).overFin hc
  let e := (extension m).overFinIso hc
  refine ⟨n, by dsimp [n, m]; omega, T, inferInstance, e.isTree_iff.mp (extension_tree m), ?_⟩
  have hg : snortMoverWins (extension m) n ∅ ∅ = false := by
    simpa only [SnortSecondPlayerWins, hc] using extension_second m (by dsimp [m]; omega)
  have h := snort_iso (extension m) T e n ∅ ∅
  simpa only [SnortSecondPlayerWins, Fintype.card_fin, Finset.image_empty] using h.trans hg

end

end MetaMathlibExt
