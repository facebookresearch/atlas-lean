/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.BayesianDirichletScore

/-!
# Markov-equivalent DAGs are connected by covered-edge reversals

A structure is a parent-set map `Pa : V → Finset V` on a finite type (edge `u → v` iff
`u ∈ Pa v`), the representation of `CoveredReversal` and the BDe score in
`CSLibExt/MachineLearning/GraphicalModels/BayesianDirichletScore.lean`. By Verma and Pearl, two
DAGs are Markov equivalent iff they have the same skeleton and the same v-structures.

## Main definitions

* `IsAcyclic Pa`: the structure has no directed cycle.
* `Adjacent Pa u w`, `IsVStructure Pa u w z`: the skeleton and the v-structures.

## Main results

* `reflTransGen_coveredReversal_of_markovEquivalent`: **Chickering's transformational
  characterization** (Chickering 1995, Theorem 2): two acyclic structures with the same skeleton
  and the same v-structures are connected by a sequence of covered-edge reversals.
* `bdeScore_eq_of_markovEquivalent`: with `bdeScore_eq_of_reflTransGen`, such structures have
  the same BDe score (score equivalence; Heckerman, Geiger and Chickering 1995).

## Proof

Strong induction on the number of differently-oriented edges. A difference yields a covered edge
of `Pa` oriented differently in `Pa'` (Chickering's procedure Find-Edge, choosing extremal nodes
by ancestor counts); reversing it keeps the structure acyclic, preserves skeleton and
v-structures, and removes one difference.

## References

* T. Verma and J. Pearl, *Equivalence and synthesis of causal models*, Proc. 6th Conference on
  Uncertainty in Artificial Intelligence (1990).
* D. M. Chickering, *A transformational characterization of equivalent Bayesian network
  structures*, Proc. 11th Conference on Uncertainty in Artificial Intelligence (1995);
  arXiv:1302.4938.
* D. Heckerman, D. Geiger and D. M. Chickering, *Learning Bayesian networks: the combination
  of knowledge and statistical data*, Machine Learning 20 (1995), 197–243.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels.BayesianDirichlet

/-- The structure has no directed cycle. -/
def IsAcyclic {V : Type*} (Pa : V → Finset V) : Prop :=
  ∀ v, ¬Relation.TransGen (fun u w => u ∈ Pa w) v v

/-- `u` and `w` are adjacent (joined by an edge in either direction). -/
def Adjacent {V : Type*} (Pa : V → Finset V) (u w : V) : Prop := u ∈ Pa w ∨ w ∈ Pa u

/-- `u → w ← z` is a v-structure: two non-adjacent distinct parents of a common child. -/
def IsVStructure {V : Type*} (Pa : V → Finset V) (u w z : V) : Prop :=
  u ≠ z ∧ u ∈ Pa w ∧ z ∈ Pa w ∧ ¬Adjacent Pa u z

/-- Adjacency is symmetric. -/
private theorem adjacent_symm {V : Type*} {Pa : V → Finset V} {u w : V}
    (h : Adjacent Pa u w) : Adjacent Pa w u :=
  Or.symm h

/-- No self-parent in an acyclic structure. -/
private theorem not_mem_self_of_acyclic {V : Type*} {Pa : V → Finset V}
    (h : IsAcyclic Pa) (x : V) : x ∉ Pa x :=
  fun hx => h x (Relation.TransGen.single hx)

/-- No 2-cycle in an acyclic structure. -/
private theorem cycle2_of_acyclic {V : Type*} {Pa : V → Finset V}
    (h : IsAcyclic Pa) {x y : V} (hxy : x ∈ Pa y) (hyx : y ∈ Pa x) : False :=
  h y (Relation.TransGen.tail (Relation.TransGen.single hyx) hxy)

/-- No 3-cycle in an acyclic structure. -/
private theorem cycle3_of_acyclic {V : Type*} {Pa : V → Finset V}
    (h : IsAcyclic Pa) {a b c : V} (hab : a ∈ Pa b) (hbc : b ∈ Pa c)
    (hca : c ∈ Pa a) : False :=
  h a (Relation.TransGen.tail
    (Relation.TransGen.tail (Relation.TransGen.single hab) hbc) hca)

/-- Minimizing the ancestor count over a nonempty finset gives an element with no member
strictly before it. -/
private theorem exists_min_anc {V : Type*} [DecidableEq V] [Fintype V] {Pa : V → Finset V}
    (h : IsAcyclic Pa) (s : Finset V) (hne : s.Nonempty) :
    ∃ y ∈ s, ∀ b ∈ s, Relation.TransGen (fun u w => u ∈ Pa w) b y → False := by
  classical
  obtain ⟨y, hys, hmin⟩ := Finset.exists_min_image s
    (fun z => (Finset.univ.filter
      (fun c => Relation.TransGen (fun u w => u ∈ Pa w) c z)).card) hne
  refine ⟨y, hys, ?_⟩
  intro b hbs hby
  have hsub : Finset.univ.filter
      (fun c => Relation.TransGen (fun u w => u ∈ Pa w) c b) ⊆
      Finset.univ.filter (fun c => Relation.TransGen (fun u w => u ∈ Pa w) c y) := by
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, hc.2.trans hby⟩
  have hbmem : b ∈ Finset.univ.filter
      (fun c => Relation.TransGen (fun u w => u ∈ Pa w) c y) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ b, hby⟩
  have hbnmem : b ∉ Finset.univ.filter
      (fun c => Relation.TransGen (fun u w => u ∈ Pa w) c b) := by
    rw [Finset.mem_filter]
    rintro ⟨-, hbb⟩
    exact h b hbb
  have hne' : Finset.univ.filter
      (fun c => Relation.TransGen (fun u w => u ∈ Pa w) c b) ≠
      Finset.univ.filter (fun c => Relation.TransGen (fun u w => u ∈ Pa w) c y) := by
    intro heq
    rw [heq] at hbnmem
    exact hbnmem hbmem
  have hlt := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne'⟩)
  have hle := hmin b hbs
  omega

/-- Maximizing the ancestor count over a nonempty finset gives an element with no member
strictly after it. -/
private theorem exists_max_anc {V : Type*} [DecidableEq V] [Fintype V] {Pa : V → Finset V}
    (h : IsAcyclic Pa) (s : Finset V) (hne : s.Nonempty) :
    ∃ y ∈ s, ∀ a ∈ s, Relation.TransGen (fun u w => u ∈ Pa w) y a → False := by
  classical
  obtain ⟨y, hys, hmax⟩ := Finset.exists_max_image s
    (fun z => (Finset.univ.filter
      (fun c => Relation.TransGen (fun u w => u ∈ Pa w) c z)).card) hne
  refine ⟨y, hys, ?_⟩
  intro a has hya
  have hsub : Finset.univ.filter
      (fun c => Relation.TransGen (fun u w => u ∈ Pa w) c y) ⊆
      Finset.univ.filter (fun c => Relation.TransGen (fun u w => u ∈ Pa w) c a) := by
    intro c hc
    rw [Finset.mem_filter] at hc ⊢
    exact ⟨hc.1, hc.2.trans hya⟩
  have hymem : y ∈ Finset.univ.filter
      (fun c => Relation.TransGen (fun u w => u ∈ Pa w) c a) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ y, hya⟩
  have hynmem : y ∉ Finset.univ.filter
      (fun c => Relation.TransGen (fun u w => u ∈ Pa w) c y) := by
    rw [Finset.mem_filter]
    rintro ⟨-, hyy⟩
    exact h y hyy
  have hne' : Finset.univ.filter
      (fun c => Relation.TransGen (fun u w => u ∈ Pa w) c y) ≠
      Finset.univ.filter (fun c => Relation.TransGen (fun u w => u ∈ Pa w) c a) := by
    intro heq
    rw [heq] at hynmem
    exact hynmem hymem
  have hlt := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne'⟩)
  have hle := hmax a has
  omega

/-- Membership at the head of the reversed edge. -/
private theorem mem_reversal_of_eq_y {V : Type*} [DecidableEq V] {Pa : V → Finset V}
    {x y : V} (hxy : x ≠ y) (u : V) :
    u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) y ↔
      u ∈ Pa x := by
  rw [Function.update_of_ne (Ne.symm hxy), Function.update_self]

/-- Membership at the tail of the reversed edge. -/
private theorem mem_reversal_of_eq_x {V : Type*} [DecidableEq V] {Pa : V → Finset V}
    {x y : V} (u : V) :
    u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) x ↔
      (u = y ∨ u ∈ Pa x) := by
  rw [Function.update_self]
  exact Finset.mem_insert

/-- Membership away from the reversed edge. -/
private theorem mem_reversal_of_ne {V : Type*} [DecidableEq V] {Pa : V → Finset V}
    {x y : V} (v : V) (hvx : v ≠ x) (hvy : v ≠ y) (u : V) :
    u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) v ↔
      u ∈ Pa v := by
  rw [Function.update_of_ne hvx, Function.update_of_ne hvy]

/-- A covered reversal only flips the edge `x → y` to `y → x`. -/
private theorem mem_reversal {V : Type*} [DecidableEq V] {Pa : V → Finset V}
    {x y : V} (hxy : x ≠ y) (hxx : x ∉ Pa x) (hPay : Pa y = insert x (Pa x))
    (u v : V) :
    u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) v ↔
      ((u = y ∧ v = x) ∨ (¬(u = x ∧ v = y) ∧ u ∈ Pa v)) := by
  by_cases hvx : v = x
  · rw [hvx, mem_reversal_of_eq_x]
    constructor
    · rintro (heq | h)
      · exact Or.inl ⟨heq, rfl⟩
      · exact Or.inr ⟨fun hcon => hxy hcon.2, h⟩
    · rintro (⟨heq, -⟩ | ⟨-, h⟩)
      · exact Or.inl heq
      · exact Or.inr h
  · by_cases hvy : v = y
    · rw [hvy, mem_reversal_of_eq_y hxy, hPay, Finset.mem_insert]
      constructor
      · intro h
        refine Or.inr ⟨?_, Or.inr h⟩
        rintro ⟨heq, -⟩
        rw [heq] at h
        exact hxx h
      · rintro (hjump | ⟨hne, (heq | h)⟩)
        · exact (hxy hjump.2.symm).elim
        · exact (hne ⟨heq, rfl⟩).elim
        · exact h
    · rw [mem_reversal_of_ne v hvx hvy]
      constructor
      · intro h
        exact Or.inr ⟨fun hcon => hvy hcon.2, h⟩
      · rintro (⟨-, hcon⟩ | ⟨-, h⟩)
        · exact absurd hcon hvx
        · exact h

/-- A covered reversal preserves the skeleton. -/
private theorem adjacent_reversal {V : Type*} [DecidableEq V] {Pa : V → Finset V}
    {x y : V} (hxy : x ≠ y) (hxx : x ∉ Pa x) (hPay : Pa y = insert x (Pa x))
    (u w : V) :
    Adjacent (Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x))) u w ↔
      Adjacent Pa u w := by
  have hxPy : x ∈ Pa y := by rw [hPay]; exact Finset.mem_insert_self x (Pa x)
  unfold Adjacent
  rw [mem_reversal hxy hxx hPay, mem_reversal hxy hxx hPay]
  constructor
  · rintro ((⟨rfl, rfl⟩ | ⟨-, h⟩) | (⟨rfl, rfl⟩ | ⟨-, h⟩))
    · exact Or.inr hxPy
    · exact Or.inl h
    · exact Or.inl hxPy
    · exact Or.inr h
  · rintro (h | h)
    · by_cases hcon : u = x ∧ w = y
      · rw [hcon.1, hcon.2]
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl (Or.inr ⟨hcon, h⟩)
    · by_cases hcon : w = x ∧ u = y
      · rw [hcon.1, hcon.2]
        exact Or.inl (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨hcon, h⟩)

/-- A covered reversal preserves v-structures. -/
private theorem isVStructure_reversal {V : Type*} [DecidableEq V] {Pa : V → Finset V}
    {x y : V} (hxy : x ≠ y) (hxx : x ∉ Pa x) (hPay : Pa y = insert x (Pa x))
    (u w z : V) :
    IsVStructure (Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x))) u w z ↔
      IsVStructure Pa u w z := by
  have hadj : ∀ a b, Adjacent
      (Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x))) a b ↔
      Adjacent Pa a b := fun a b => adjacent_reversal hxy hxx hPay a b
  unfold IsVStructure
  rw [hadj]
  by_cases hwy : w = y
  · rw [hwy, mem_reversal_of_eq_y hxy u, mem_reversal_of_eq_y hxy z, hPay,
      Finset.mem_insert, Finset.mem_insert]
    constructor
    · rintro ⟨huz, hu, hz, hnadj⟩
      exact ⟨huz, Or.inr hu, Or.inr hz, hnadj⟩
    · rintro ⟨huz, (hu | hu), (hz | hz), hnadj⟩
      · exact (huz (hu.trans hz.symm)).elim
      · exact (hnadj (Or.inr (by rw [hu]; exact hz))).elim
      · exact (hnadj (Or.inl (by rw [hz]; exact hu))).elim
      · exact ⟨huz, hu, hz, hnadj⟩
  · by_cases hwx : w = x
    · rw [hwx, mem_reversal_of_eq_x u, mem_reversal_of_eq_x z]
      constructor
      · rintro ⟨huz, (hu | hu), (hz | hz), hnadj⟩
        · exact (huz (hu.trans hz.symm)).elim
        · have hzy : z ∈ Pa y := by
            rw [hPay]; exact Finset.mem_insert.mpr (Or.inr hz)
          exact (hnadj (Or.inr (by rw [hu]; exact hzy))).elim
        · have huy : u ∈ Pa y := by
            rw [hPay]; exact Finset.mem_insert.mpr (Or.inr hu)
          exact (hnadj (Or.inl (by rw [hz]; exact huy))).elim
        · exact ⟨huz, hu, hz, hnadj⟩
      · rintro ⟨huz, hu, hz, hnadj⟩
        exact ⟨huz, Or.inr hu, Or.inr hz, hnadj⟩
    · rw [mem_reversal_of_ne w hwx hwy u, mem_reversal_of_ne w hwx hwy z]

/-- A covered reversal of an acyclic structure is acyclic. -/
private theorem acyclic_reversal {V : Type*} [DecidableEq V] {Pa : V → Finset V}
    {x y : V} (h : IsAcyclic Pa) (hxy : x ≠ y) (hPay : Pa y = insert x (Pa x)) :
    IsAcyclic (Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x))) := by
  have hxx : x ∉ Pa x := not_mem_self_of_acyclic h x
  have hno : ∀ a b, Relation.TransGen
      (fun u w => u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) w)
      a b →
      (a = x → b ≠ y) ∧
        (Relation.ReflTransGen (fun u w => u ∈ Pa w) a b ∨
          (Relation.ReflTransGen (fun u w => u ∈ Pa w) a y ∧
            Relation.ReflTransGen (fun u w => u ∈ Pa w) x b)) := by
    intro a b hab
    refine Relation.TransGen.rec
      (motive := fun b _ => (a = x → b ≠ y) ∧
        (Relation.ReflTransGen (fun u w => u ∈ Pa w) a b ∨
          (Relation.ReflTransGen (fun u w => u ∈ Pa w) a y ∧
            Relation.ReflTransGen (fun u w => u ∈ Pa w) x b))) ?_ ?_ hab
    · intro b' s
      by_cases hj : a = y ∧ b' = x
      · rcases hj with ⟨ha, hb⟩
        refine ⟨?_, Or.inr ?_⟩
        · intro ha' hb'
          exact hxy (ha'.symm.trans ha)
        · refine ⟨?_, ?_⟩
          · rw [ha]
          · rw [hb]
      · obtain ⟨hnxy, hab'⟩ := ((mem_reversal hxy hxx hPay a b').mp s).resolve_left hj
        refine ⟨?_, Or.inl (Relation.ReflTransGen.single hab')⟩
        intro ha hb
        exact hnxy ⟨ha, hb⟩
    · intro b' c' h1 s ih
      have hs := (mem_reversal hxy hxx hPay _ _).mp s
      refine ⟨?_, ?_⟩
      · intro ha hb
        rw [hb] at hs
        rcases hs with (⟨-, hjyx⟩ | ⟨hn, hmy⟩)
        · exact hxy hjyx.symm
        · rw [hPay, Finset.mem_insert] at hmy
          rcases hmy with (heq | hmx)
          · exact (hn ⟨heq, rfl⟩).elim
          · have hxm : Relation.ReflTransGen (fun u w => u ∈ Pa w) x b' := by
              rcases ih.2 with h | ⟨-, h⟩
              · rw [ha] at h; exact h
              · exact h
            rcases Relation.reflTransGen_iff_eq_or_transGen.mp hxm with (heq | htrans)
            · rw [heq] at hmx; exact h x (Relation.TransGen.single hmx)
            · exact h x (Relation.TransGen.tail htrans hmx)
      · rcases hs with (⟨hmy, hbx⟩ | ⟨-, hmb⟩)
        · rw [hbx]
          refine Or.inr ⟨?_, Relation.ReflTransGen.refl⟩
          rcases ih.2 with h | ⟨h, -⟩
          · rw [hmy] at h; exact h
          · exact h
        · rcases ih.2 with h | ⟨h1', h2'⟩
          · exact Or.inl (h.tail hmb)
          · exact Or.inr ⟨h1', h2'.tail hmb⟩
  have hT : ∀ a b, Relation.TransGen
      (fun u w => u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) w)
      a b →
      Relation.TransGen (fun u w => u ∈ Pa w) a b ∨
        (Relation.ReflTransGen
          (fun u w => u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) w)
          a y ∧
          Relation.ReflTransGen
            (fun u w => u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) w)
            x b) := by
    intro a b hab
    refine Relation.TransGen.rec
      (motive := fun b _ => Relation.TransGen (fun u w => u ∈ Pa w) a b ∨
        (Relation.ReflTransGen
          (fun u w => u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) w)
          a y ∧
          Relation.ReflTransGen
            (fun u w => u ∈ Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)) w)
            x b)) ?_ ?_ hab
    · intro b' s
      by_cases hj : a = y ∧ b' = x
      · rcases hj with ⟨ha, hb⟩
        rw [ha, hb]
        exact Or.inr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
      · obtain ⟨-, hab'⟩ := ((mem_reversal hxy hxx hPay a b').mp s).resolve_left hj
        exact Or.inl (Relation.TransGen.single hab')
    · intro b' c' h1 s ih
      have hs := (mem_reversal hxy hxx hPay _ _).mp s
      rcases hs with (⟨hmy, hbx⟩ | ⟨-, hmb⟩)
      · rw [hbx]
        rw [hmy] at h1
        exact Or.inr ⟨h1.to_reflTransGen, Relation.ReflTransGen.refl⟩
      · rcases ih with h | ⟨h1', h2'⟩
        · exact Or.inl (h.tail hmb)
        · exact Or.inr ⟨h1', h2'.tail s⟩
  intro v hv
  rcases hT v v hv with hcycle | ⟨hvy, hxv⟩
  · exact h v hcycle
  · have hxy1 := hxv.trans hvy
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hxy1 with (heq | htrans)
    · exact hxy heq.symm
    · have hQ := hno x y htrans
      exact hQ.1 rfl rfl

/-- The ordered pairs where `Pa` and `Pa'` orient the shared edge differently. -/
private def diffEdges {V : Type*} [DecidableEq V] [Fintype V] (Pa Pa' : V → Finset V) :
    Finset (V × V) :=
  Finset.univ.filter (fun p : V × V => p.1 ∈ Pa p.2 ∧ p.2 ∈ Pa' p.1)

/-- No differently-oriented edges means the structures agree. -/
private theorem eq_of_diffEdges_empty {V : Type*} [DecidableEq V] [Fintype V]
    {Pa Pa' : V → Finset V}
    (hskel : ∀ u w, Adjacent Pa u w ↔ Adjacent Pa' u w)
    (hempty : diffEdges Pa Pa' = ∅) : Pa = Pa' := by
  funext v
  ext u
  constructor
  · intro huv
    rcases (hskel u v).mp (Or.inl huv) with h | h
    · exact h
    · have hmem : (u, v) ∈ diffEdges Pa Pa' := by
        simp only [diffEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨huv, h⟩
      rw [hempty] at hmem
      exact absurd hmem (Finset.notMem_empty _)
  · intro huv
    rcases (hskel u v).mpr (Or.inl huv) with h | h
    · exact h
    · have hmem : (v, u) ∈ diffEdges Pa Pa' := by
        simp only [diffEdges, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h, huv⟩
      rw [hempty] at hmem
      exact absurd hmem (Finset.notMem_empty _)

/-- Reversing a differently-oriented covered edge strictly reduces the difference count. -/
private theorem card_diffEdges_lt_of_reversal {V : Type*} [DecidableEq V] [Fintype V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (h' : IsAcyclic Pa')
    {x y : V} (hxy : x ≠ y) (hxPy : x ∈ Pa y) (hyx : y ∈ Pa' x)
    (hPay : Pa y = insert x (Pa x)) :
    (diffEdges (Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
      Pa').card < (diffEdges Pa Pa').card := by
  have hxx : x ∉ Pa x := not_mem_self_of_acyclic h x
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro p hp
    obtain ⟨u, v⟩ := p
    simp only [diffEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨huv1, hvu'⟩ := hp
    by_cases hj : u = y ∧ v = x
    · rcases hj with ⟨ha, hb⟩
      rw [ha, hb] at hvu'
      exact (cycle2_of_acyclic h' hvu' hyx).elim
    · obtain ⟨-, huv⟩ := ((mem_reversal hxy hxx hPay u v).mp huv1).resolve_left hj
      exact ⟨huv, hvu'⟩
  · intro heq
    have hmem : (x, y) ∈ diffEdges Pa Pa' := by
      simp only [diffEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hxPy, hyx⟩
    have hnmem : (x, y) ∉ diffEdges
        (Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x))) Pa' := by
      simp only [diffEdges, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨hxy1, -⟩
      have hcase := (mem_reversal hxy hxx hPay x y).mp hxy1
      rcases hcase with (⟨heq1, -⟩ | ⟨hn, -⟩)
      · exact hxy heq1
      · exact hn ⟨rfl, rfl⟩
    rw [←heq] at hmem
    exact hnmem hmem

/-- Chickering's edge selection: a difference yields a covered, differently-oriented edge. -/
private theorem exists_covered_of_diffEdges_nonempty {V : Type*} [DecidableEq V] [Fintype V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (h' : IsAcyclic Pa')
    (hskel : ∀ u w, Adjacent Pa u w ↔ Adjacent Pa' u w)
    (hv : ∀ u w z, IsVStructure Pa u w z ↔ IsVStructure Pa' u w z)
    (hne : (diffEdges Pa Pa').Nonempty) :
    ∃ x y, x ≠ y ∧ x ∈ Pa y ∧ y ∈ Pa' x ∧ Pa y = insert x (Pa x) := by
  classical
  obtain ⟨⟨a, b⟩, hab⟩ := hne
  simp only [diffEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hab
  obtain ⟨hab1, hab2⟩ := hab
  have hS : (Finset.univ.filter
      (fun c => ∃ a, a ∈ Pa c ∧ c ∈ Pa' a)).Nonempty := by
    refine ⟨b, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ b, a, hab1, hab2⟩
  obtain ⟨y, hyS, hymin⟩ := exists_min_anc h _ hS
  rw [Finset.mem_filter] at hyS
  obtain ⟨-, x0, hx0y, hyx0⟩ := hyS
  have hC : ((Pa y).filter (fun c => y ∈ Pa' c)).Nonempty := by
    refine ⟨x0, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hx0y, hyx0⟩
  obtain ⟨x, hxC, hxmax⟩ := exists_max_anc h _ hC
  rw [Finset.mem_filter] at hxC
  obtain ⟨hxPy, hyx⟩ := hxC
  have hxy : x ≠ y := by
    intro heq
    rw [←heq] at hxPy
    exact not_mem_self_of_acyclic h x hxPy
  refine ⟨x, y, hxy, hxPy, hyx, ?_⟩
  ext z
  rw [Finset.mem_insert]
  constructor
  · intro hzy
    by_cases hzx : z = x
    · exact Or.inl hzx
    · right
      by_cases hadj : Adjacent Pa z x
      · rcases hadj with h | h
        · exact h
        · rcases (hskel x z).mp (Or.inl h) with hxz' | hzx'
          · rcases (hskel z y).mp (Or.inl hzy) with hzy' | hyz'
            · exact (cycle3_of_acyclic h' hyx hxz' hzy').elim
            · have hzC : z ∈ (Pa y).filter (fun c => y ∈ Pa' c) := by
                rw [Finset.mem_filter]
                exact ⟨hzy, hyz'⟩
              exact (hxmax z hzC (Relation.TransGen.single h)).elim
          · have hzS : z ∈ Finset.univ.filter
                (fun c => ∃ a, a ∈ Pa c ∧ c ∈ Pa' a) := by
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_univ z, x, h, hzx'⟩
            exact (hymin z hzS (Relation.TransGen.single hzy)).elim
      · have hvs : IsVStructure Pa z y x := ⟨hzx, hzy, hxPy, hadj⟩
        have hvs' := (hv z y x).mp hvs
        obtain ⟨-, -, hxPy', -⟩ := hvs'
        exact (cycle2_of_acyclic h' hxPy' hyx).elim
  · rintro (heq | hw)
    · rw [heq]; exact hxPy
    · by_contra hnzy
      have hzw : z ≠ y := by
        intro heq
        rw [heq] at hw
        exact (cycle2_of_acyclic h hxPy hw).elim
      by_cases hadj : Adjacent Pa z y
      · rcases hadj with hzy' | hyz'
        · exact (hnzy hzy').elim
        · exact (cycle3_of_acyclic h hw hxPy hyz').elim
      · rcases (hskel z x).mp (Or.inl hw) with hzx' | hxw'
        · have hnadj' : ¬Adjacent Pa' y z :=
            fun hh => hadj (adjacent_symm ((hskel y z).mpr hh))
          have hvs' : IsVStructure Pa' y x z := ⟨Ne.symm hzw, hyx, hzx', hnadj'⟩
          have hvs := (hv y x z).mpr hvs'
          obtain ⟨-, hyxPa, -, -⟩ := hvs
          exact (cycle2_of_acyclic h hxPy hyxPa).elim
        · have hxS : x ∈ Finset.univ.filter
              (fun c => ∃ a, a ∈ Pa c ∧ c ∈ Pa' a) := by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ x, z, hw, hxw'⟩
          exact hymin x hxS (Relation.TransGen.single hxPy)

/-- Induction on the difference count. -/
private theorem reflTransGen_of_le_card {V : Type*} [DecidableEq V] [Fintype V]
    {Pa' : V → Finset V} (h' : IsAcyclic Pa') :
    ∀ (n : ℕ) (Pa : V → Finset V), IsAcyclic Pa →
      (∀ u w, Adjacent Pa u w ↔ Adjacent Pa' u w) →
      (∀ u w z, IsVStructure Pa u w z ↔ IsVStructure Pa' u w z) →
      (diffEdges Pa Pa').card ≤ n → Relation.ReflTransGen CoveredReversal Pa Pa' := by
  intro n
  induction n with
  | zero =>
    intro Pa h hskel hv hle
    have hcard : (diffEdges Pa Pa').card = 0 := Nat.le_zero.mp hle
    have hempty : diffEdges Pa Pa' = ∅ := Finset.card_eq_zero.mp hcard
    have heq : Pa = Pa' := eq_of_diffEdges_empty hskel hempty
    rw [heq]
  | succ n ih =>
    intro Pa h hskel hv hle
    by_cases hempty : diffEdges Pa Pa' = ∅
    · have heq : Pa = Pa' := eq_of_diffEdges_empty hskel hempty
      rw [heq]
    · have hne := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨x, y, hxy, hxPy, hyx, hPay⟩ :=
        exists_covered_of_diffEdges_nonempty h h' hskel hv hne
      have hxx : x ∉ Pa x := not_mem_self_of_acyclic h x
      have hac1 : IsAcyclic
          (Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x))) :=
        acyclic_reversal h hxy hPay
      have hskel1 : ∀ u w, Adjacent
          (Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x))) u w ↔
          Adjacent Pa' u w :=
        fun u w => (adjacent_reversal hxy hxx hPay u w).trans (hskel u w)
      have hv1 : ∀ u w z, IsVStructure
          (Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x))) u w z ↔
          IsVStructure Pa' u w z :=
        fun u w z => (isVStructure_reversal hxy hxx hPay u w z).trans (hv u w z)
      have hlt := card_diffEdges_lt_of_reversal h h' hxy hxPy hyx hPay
      have hle' : (diffEdges
          (Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x)))
          Pa').card ≤ n := by omega
      have ihrt := ih _ hac1 hskel1 hv1 hle'
      have hCr : CoveredReversal Pa
          (Function.update (Function.update Pa y (Pa x)) x (insert y (Pa x))) :=
        ⟨x, y, hxy, hPay, rfl⟩
      exact Relation.ReflTransGen.head hCr ihrt

/-- **Chickering's transformational characterization** (1995): two acyclic structures with the
same skeleton and the same v-structures (Markov equivalent by Verma and Pearl) are connected by
a sequence of covered-edge reversals. -/
theorem reflTransGen_coveredReversal_of_markovEquivalent {V : Type*} [DecidableEq V]
    [Finite V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (h' : IsAcyclic Pa')
    (hskel : ∀ u w, Adjacent Pa u w ↔ Adjacent Pa' u w)
    (hv : ∀ u w z, IsVStructure Pa u w z ↔ IsVStructure Pa' u w z) :
    Relation.ReflTransGen CoveredReversal Pa Pa' := by
  have _inst : Fintype V := Fintype.ofFinite V
  exact reflTransGen_of_le_card h' _ Pa h hskel hv le_rfl

/-- **Score equivalence of BDe** (Heckerman, Geiger and Chickering 1995): two acyclic
structures with the same skeleton and the same v-structures have the same BDe score. -/
theorem bdeScore_eq_of_markovEquivalent {V : Type*} [DecidableEq V] [Fintype V]
    {σ : V → Type*} [∀ v, Fintype (σ v)] [∀ v, DecidableEq (σ v)] [∀ v, Nonempty (σ v)]
    (p : ((v : V) → σ v) → ℝ) (hp : ∀ x, 0 < p x) {ess : ℝ} (hess : 0 < ess)
    (D : List ((v : V) → σ v)) {Pa Pa' : V → Finset V} (h : IsAcyclic Pa)
    (h' : IsAcyclic Pa') (hskel : ∀ u w, Adjacent Pa u w ↔ Adjacent Pa' u w)
    (hv : ∀ u w z, IsVStructure Pa u w z ↔ IsVStructure Pa' u w z) :
    bdeScore p ess D Pa' = bdeScore p ess D Pa := by
  have hrt := reflTransGen_coveredReversal_of_markovEquivalent h h' hskel hv
  exact bdeScore_eq_of_reflTransGen p hp hess D hrt

end Cslib.MachineLearning.GraphicalModels.BayesianDirichlet
