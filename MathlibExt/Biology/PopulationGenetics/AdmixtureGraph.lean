/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatistics

/-!
# Admixture graphs

An admixture graph (Patterson et al. 2012, Appendix) is a finite rooted directed acyclic graph
whose nodes are populations. Every non-root node has one parent (a tree edge) or two parents
(an admixture node); the lineage of a gene sampled in `X` moves to parent `Y` with probability
`prop X Y`, so the proportions on the edges out of a non-root node sum to `1` (one parent:
proportion `1`; two parents: `α` and `1 - α` with `α ∈ [0, 1]`).

Edges are pairs `(child, parent)`. Tracing a lineage from `X` toward the root, choosing parents
with the admixture proportions,

* `visit X c` is the probability that the lineage passes through node `c`, defined by
  first-step analysis: `visit X X = 1` and, for `c ≠ X`,
  `visit X c = ∑ Y ∈ parents X, prop X Y * visit Y c`;
* `weight X e = visit X c * prop c p` is the probability that it traverses the edge
  `e = (c, p)`; `weight_eq_sum_paths` identifies it with the sum, over the root-ward paths
  from `X` through `e`, of the products of the proportions along the path.

These weights are the coefficients of the seed's `DriftModel`: with drift increments on the
edges, the allele frequency of `X` is `root + ∑ e, weight X e * incr e`.

## Main results

* `AdmixtureGraph.weight_nonneg`, `AdmixtureGraph.weight_le_one`: weights are probabilities.
* `AdmixtureGraph.visit_root`: every lineage reaches the root.
* `AdmixtureGraph.weight_eq`: the first-step recursion
  `w X e = ∑ Y ∈ parents X, prop X Y * w Y e + [e = (X, p)] * prop X p`;
  `AdmixtureGraph.weight_admixture` and `AdmixtureGraph.weight_tree` specialize it.
* `AdmixtureGraph.weight_eq_sum_paths`: the path-sum form of the weights.
* `AdmixtureGraph.weight_eq_zero_or_one`: on a tree (no admixture node) weights are `0` or `1`.
* `AdmixtureGraph.driftModel`: the drift model induced by a graph and edge increments;
  `AdmixtureGraph.hasBinaryLoadings_of_isTree`: a tree-shaped graph induces binary loadings,
  so `AdmixtureGraph.f3_nonneg_of_isTree`: on a tree `f3 ≥ 0` (the three-population test).
* `AdmixtureGraph.f3_admixture`: for an admixture node `X` with parents `A`, `B`,
  `f3 X A B = α² ℓ_{XA} + β² ℓ_{XB} - α β f2 A B` (`α + β = 1`, `ℓ` the drift lengths of the
  admixture edges); with no drift on the admixture edges this is the seed's
  `f3 = -α (1 - α) f2` (`AdmixtureGraph.f3_admixture_of_len_eq_zero`).

## References

* N. Patterson, P. Moorjani, Y. Luo, S. Mallick, N. Rohland, Y. Zhan, T. Genschoreck,
  T. Webster, D. Reich, *Ancient admixture in human history*, Genetics 192 (2012), 1065–1093,
  Appendix.
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics

namespace MathlibExt.Biology.PopulationGenetics

/-- An admixture graph on the nodes `V` (Patterson et al. 2012): a rooted directed acyclic
graph in which every non-root node has one or two parents, with admixture proportions.

* `parents X` are the parents of `X`, the root has none, every other node has one or two;
* `prop X Y` is the probability that a lineage in `X` descends from parent `Y`: nonnegative,
  summing to `1` over the parents of a non-root node, and `0` off the parent set;
* the parent relation is well founded, i.e. the graph is acyclic (`V` is finite in all
  results). -/
structure AdmixtureGraph (V : Type*) where
  /-- The root (ancestral population). -/
  root : V
  /-- The parents of each node. -/
  parents : V → Finset V
  /-- Admixture proportions: `prop X Y` is the share of ancestry of `X` from parent `Y`. -/
  prop : V → V → ℝ
  /-- The root has no parent. -/
  parents_root : parents root = ∅
  /-- Every non-root node has one parent (tree edge) or two parents (admixture node). -/
  card_parents : ∀ X, X ≠ root → (parents X).card = 1 ∨ (parents X).card = 2
  /-- Proportions are nonnegative. -/
  prop_nonneg : ∀ X Y, 0 ≤ prop X Y
  /-- Proportions vanish off the parent set. -/
  prop_eq_zero : ∀ X Y, Y ∉ parents X → prop X Y = 0
  /-- The proportions of a non-root node sum to `1`. -/
  sum_prop : ∀ X, X ≠ root → ∑ Y ∈ parents X, prop X Y = 1
  /-- The graph is acyclic: the parent relation is well founded. -/
  wf : WellFounded fun Y X => Y ∈ parents X

namespace AdmixtureGraph

variable {V : Type*} [DecidableEq V] (G : AdmixtureGraph V)

/-- The edges `(child, parent)` of the graph. -/
abbrev Edge : Type _ := {e : V × V // e.2 ∈ G.parents e.1}

/-- `visit X c` is the probability that the lineage of a gene sampled in `X`, traced toward the
root with parents chosen according to the admixture proportions, passes through `c`. -/
noncomputable def visit (X c : V) : ℝ :=
  G.wf.fix (C := fun _ => ℝ)
    (fun X ih => if X = c then 1 else ∑ Y ∈ (G.parents X).attach, G.prop X Y * ih Y Y.2) X

/-- `weight X e` is the probability that the lineage of a gene sampled in `X` traverses the edge
`e = (c, p)`: it reaches `c` and then descends from `p`. -/
noncomputable def weight (X : V) (e : G.Edge) : ℝ := G.visit X e.1.1 * G.prop e.1.1 e.1.2

/-- The probability of a root-ward path `[v₀, v₁, …, v_k]`: the product of the proportions
`prop vᵢ vᵢ₊₁`. -/
def pathProb : List V → ℝ
  | a :: b :: l => G.prop a b * pathProb (b :: l)
  | _ => 1

/-- The root-ward paths from `X`: the lists `[X = v₀, v₁, …, v_k = root]` with each `vᵢ₊₁` a
parent of `vᵢ`. -/
noncomputable def paths (X : V) : Finset (List V) :=
  G.wf.fix (C := fun _ => Finset (List V))
    (fun X ih => if G.parents X = ∅ then {[X]} else
      (G.parents X).attach.biUnion fun Y => (ih Y Y.2).image (List.cons X)) X

/-- First-step equation for `visit`. -/
theorem visit_eq (X c : V) :
    G.visit X c = if X = c then 1 else ∑ Y ∈ G.parents X, G.prop X Y * G.visit Y c := by
  rw [visit, WellFounded.fix_eq]
  split_ifs
  · rfl
  · exact Finset.sum_attach (G.parents X) fun Y => G.prop X Y * G.visit Y c

/-- A lineage passes through its own node with probability `1`. -/
@[simp] theorem visit_self (X : V) : G.visit X X = 1 := by
  simp [visit_eq G X X]

/-- Visit probabilities are nonnegative. -/
theorem visit_nonneg (X c : V) : 0 ≤ G.visit X c := by
  induction X using G.wf.induction with
  | _ X ih =>
    rw [visit_eq]
    split_ifs
    · exact zero_le_one
    · exact Finset.sum_nonneg fun Y hY => mul_nonneg (G.prop_nonneg X Y) (ih Y hY)

/-- Visit probabilities are at most `1`. -/
theorem visit_le_one (X c : V) : G.visit X c ≤ 1 := by
  induction X using G.wf.induction with
  | _ X ih =>
    rw [visit_eq]
    split_ifs
    · exact le_rfl
    · by_cases hX : X = G.root
      · simp [hX, G.parents_root]
      · calc ∑ Y ∈ G.parents X, G.prop X Y * G.visit Y c
            ≤ ∑ Y ∈ G.parents X, G.prop X Y := Finset.sum_le_sum fun Y hY =>
              mul_le_of_le_one_right (G.prop_nonneg X Y) (ih Y hY)
          _ = 1 := G.sum_prop X hX

/-- Every lineage reaches the root. -/
theorem visit_root (X : V) : G.visit X G.root = 1 := by
  induction X using G.wf.induction with
  | _ X ih =>
    rw [visit_eq]
    split_ifs with hX
    · rfl
    · rw [← G.sum_prop X hX]
      exact Finset.sum_congr rfl fun Y hY => by rw [ih Y hY, mul_one]

/-- First-step equation for `paths`. -/
theorem paths_eq (X : V) :
    G.paths X = if G.parents X = ∅ then {[X]} else
      (G.parents X).biUnion fun Y => (G.paths Y).image (List.cons X) := by
  rw [paths, WellFounded.fix_eq]
  split_ifs
  · rfl
  · ext π
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, exists_prop]
    rfl

omit [DecidableEq V] in
/-- Admixture proportions are at most `1`. -/
theorem prop_le_one (X Y : V) : G.prop X Y ≤ 1 := by
  by_cases hY : Y ∈ G.parents X
  · have hX : X ≠ G.root := by
      rintro rfl
      simp [G.parents_root] at hY
    rw [← G.sum_prop X hX]
    exact Finset.single_le_sum (fun Z _ => G.prop_nonneg X Z) hY
  · rw [G.prop_eq_zero X Y hY]
    exact zero_le_one

private theorem visit_eq_zero_of_transGen {V : Type*} [DecidableEq V]
    (G : AdmixtureGraph V) {X Y : V}
    (h : Relation.TransGen (fun a b => a ∈ G.parents b) Y X) : G.visit Y X = 0 := by
  induction Y using G.wf.induction generalizing X with
  | _ Y ih =>
    have hYX : Y ≠ X := by
      rintro rfl
      exact G.wf.transGen.irrefl.irrefl _ h
    rw [visit_eq, ite_eq_right hYX]
    exact Finset.sum_eq_zero fun Z hZ => by
      rw [ih Z hZ (Relation.TransGen.head hZ h), mul_zero]

/-- Acyclicity: a lineage from a parent `Y` of `X` never passes through `X`. -/
theorem visit_eq_zero_of_mem_parents {X Y : V} (h : Y ∈ G.parents X) : G.visit Y X = 0 := by
  exact visit_eq_zero_of_transGen G (Relation.TransGen.single h)

/-- Lineage weights are nonnegative. -/
theorem weight_nonneg (X : V) (e : G.Edge) : 0 ≤ G.weight X e := by
  exact mul_nonneg (G.visit_nonneg _ _) (G.prop_nonneg _ _)

/-- Lineage weights are at most `1`. -/
theorem weight_le_one (X : V) (e : G.Edge) : G.weight X e ≤ 1 := by
  simpa [weight] using mul_le_mul (G.visit_le_one X e.1.1) (G.prop_le_one e.1.1 e.1.2)
    (G.prop_nonneg _ _) zero_le_one

/-- First-step recursion for lineage weights: a lineage from `X` traverses `e` either as its
first step (if `e` starts at `X`) or after moving to a parent `Y`, chosen with probability
`prop X Y`. -/
theorem weight_eq (X : V) (e : G.Edge) :
    G.weight X e = ∑ Y ∈ G.parents X, G.prop X Y * G.weight Y e +
      if e.1.1 = X then G.prop X e.1.2 else 0 := by
  obtain ⟨⟨c, p⟩, hp⟩ := e
  simp only [weight]
  by_cases hc : c = X
  · subst hc
    rw [visit_self, one_mul, ite_eq_left rfl,
      Finset.sum_eq_zero fun Y hY => by rw [G.visit_eq_zero_of_mem_parents hY]; ring, zero_add]
  · rw [visit_eq, ite_eq_right fun h => hc h.symm, ite_eq_right hc, Finset.sum_mul, add_zero]
    exact Finset.sum_congr rfl fun Y _ => by ring

/-- The recursion at an admixture node `X` with parents `A ≠ B`: with `α = prop X A`,
`w X = α w A + (1 - α) w B + w₀`, where `w₀` puts weight `α` on the edge `(X, A)`,
`1 - α` on `(X, B)` and `0` elsewhere. -/
theorem weight_admixture {X A B : V} (hX : G.parents X = {A, B}) (hAB : A ≠ B) :
    G.weight X = G.prop X A • G.weight A + (1 - G.prop X A) • G.weight B +
      fun e => if e.1.1 = X then G.prop X e.1.2 else 0 := by
  have hXr : X ≠ G.root := by
    rintro rfl
    exact Finset.insert_ne_empty A {B} (hX.symm.trans G.parents_root)
  have hsum := G.sum_prop X hXr
  rw [hX, Finset.sum_pair hAB] at hsum
  funext e
  rw [weight_eq, hX, Finset.sum_pair hAB]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [show G.prop X B = 1 - G.prop X A by linarith]

/-- The recursion at a tree node `X` with the single parent `Y`: `w X = w Y + 1_{(X, Y)}`. -/
theorem weight_tree {X Y : V} (hX : G.parents X = {Y}) :
    G.weight X = G.weight Y + fun e => if e.1.1 = X then 1 else 0 := by
  have hXr : X ≠ G.root := by
    rintro rfl
    simp [G.parents_root] at hX
  have h1 : G.prop X Y = 1 := by simpa [hX] using G.sum_prop X hXr
  funext e
  rw [weight_eq, hX, Finset.sum_singleton, h1, one_mul]
  simp only [Pi.add_apply]
  congr 1
  split_ifs with h
  · have he := e.2
    rw [h, hX, Finset.mem_singleton] at he
    rw [he, h1]
  · rfl

private theorem path_head {V : Type*} [DecidableEq V] (G : AdmixtureGraph V)
    (X : V) {π : List V} (hπ : π ∈ G.paths X) : π.head? = some X := by
  rw [paths_eq] at hπ
  split_ifs at hπ
  · have h := Finset.mem_singleton.mp hπ
    subst π
    rfl
  · obtain ⟨Y, _, hπ⟩ := Finset.mem_biUnion.mp hπ
    obtain ⟨π', _, rfl⟩ := Finset.mem_image.mp hπ
    rfl

private theorem path_avoids_descendant {V : Type*} [DecidableEq V]
    (G : AdmixtureGraph V) {X Y : V}
    (h : Relation.TransGen (fun a b => a ∈ G.parents b) Y X)
    {π : List V} (hπ : π ∈ G.paths Y) : X ∉ π := by
  induction Y using G.wf.induction generalizing X π with
  | _ Y ih =>
    have hYX : Y ≠ X := by
      rintro rfl
      exact G.wf.transGen.irrefl.irrefl _ h
    rw [paths_eq] at hπ
    split_ifs at hπ
    · have hπ' := Finset.mem_singleton.mp hπ
      subst π
      simpa using hYX.symm
    · obtain ⟨Z, hZ, hπ⟩ := Finset.mem_biUnion.mp hπ
      obtain ⟨π', hπ', rfl⟩ := Finset.mem_image.mp hπ
      simp only [List.mem_cons, not_or]
      exact ⟨hYX.symm, ih Z hZ (Relation.TransGen.head hZ h) hπ'⟩

private theorem path_images_disjoint {V : Type*} [DecidableEq V]
    (G : AdmixtureGraph V) (X : V) {Y Z : V} (hYZ : Y ≠ Z) :
    Disjoint ((G.paths Y).image (List.cons X)) ((G.paths Z).image (List.cons X)) := by
  apply Finset.disjoint_left.mpr
  intro π hY hZ
  obtain ⟨πY, hπY, rfl⟩ := Finset.mem_image.mp hY
  obtain ⟨πZ, hπZ, heq⟩ := Finset.mem_image.mp hZ
  have hπ : πZ = πY := List.cons.inj heq |>.2
  have hh := path_head G Y hπY
  rw [← hπ, path_head G Z hπZ] at hh
  exact hYZ (Option.some.inj hh).symm

private theorem sum_pathProb {V : Type*} [DecidableEq V] (G : AdmixtureGraph V)
    (X : V) : ∑ π ∈ G.paths X, G.pathProb π = 1 := by
  induction X using G.wf.induction with
  | _ X ih =>
    rw [paths_eq]
    split_ifs with hX
    · simp [pathProb]
    · rw [Finset.sum_biUnion]
      · have hXr : X ≠ G.root := by
          rintro rfl
          exact hX G.parents_root
        rw [← G.sum_prop X hXr]
        apply Finset.sum_congr rfl
        intro Y hY
        rw [Finset.sum_image]
        · calc
            ∑ π ∈ G.paths Y, G.pathProb (X :: π) =
                ∑ π ∈ G.paths Y, G.prop X Y * G.pathProb π := by
              apply Finset.sum_congr rfl
              intro π hπ
              have hh := path_head G Y hπ
              cases π with
              | nil => simp at hh
              | cons Z l =>
                have hZ : Z = Y := Option.some.inj hh
                subst Z
                rfl
            _ = G.prop X Y := by rw [← Finset.mul_sum, ih Y hY, mul_one]
        · intro a _ b _ h
          exact List.cons.inj h |>.2
      · intro Y _ Z _ hYZ
        exact path_images_disjoint G X hYZ

private theorem path_edge_step {V : Type*} [DecidableEq V] (G : AdmixtureGraph V)
    (X Y : V) (hY : Y ∈ G.parents X) (e : G.Edge)
    {π : List V} (hπ : π ∈ G.paths Y) :
    (if e.1 ∈ (X :: π).zip (X :: π).tail then G.pathProb (X :: π) else 0) =
      G.prop X Y * (if e.1 ∈ π.zip π.tail then G.pathProb π else 0) +
        if e.1 = (X, Y) then G.prop X Y * G.pathProb π else 0 := by
  have hh := path_head G Y hπ
  cases π with
  | nil => simp at hh
  | cons Z l =>
    have hZ : Z = Y := Option.some.inj hh
    subst Z
    have hnot : e.1 = (X, Y) → e.1 ∉ (Y :: l).zip (Y :: l).tail := by
      intro he hm
      have hx := path_avoids_descendant G (Relation.TransGen.single hY) hπ
      rw [he] at hm
      exact hx (List.of_mem_zip hm).1
    change (if e.1 ∈ (X, Y) :: (Y :: l).zip (Y :: l).tail
      then G.prop X Y * G.pathProb (Y :: l) else 0) = _
    simp only [List.mem_cons]
    by_cases he : e.1 = (X, Y)
    · rw [ite_eq_left (Or.inl he), ite_eq_right (hnot he), ite_eq_left he]
      simp
    · simp only [he, false_or, ite_false, mul_ite, mul_zero, add_zero]

private theorem sum_first_edge {V : Type*} [DecidableEq V] (G : AdmixtureGraph V)
    (X : V) (e : G.Edge) :
    (∑ Y ∈ G.parents X, if e.1 = (X, Y) then G.prop X Y else 0) =
      if e.1.1 = X then G.prop X e.1.2 else 0 := by
  by_cases hc : e.1.1 = X
  · have hp : e.1.2 ∈ G.parents X := by simpa [hc] using e.2
    rw [ite_eq_left hc]
    rw [Finset.sum_eq_single e.1.2]
    · have he : e.1 = (X, e.1.2) := Prod.ext hc rfl
      exact ite_eq_left he
    · intro Y _ hY
      have he : e.1 ≠ (X, Y) := by
        intro he
        exact hY (congrArg Prod.snd he).symm
      simp [he]
    · exact fun h => (h hp).elim
  · rw [ite_eq_right hc]
    apply Finset.sum_eq_zero
    intro Y _
    have he : e.1 ≠ (X, Y) := by
      intro he
      exact hc (congrArg Prod.fst he)
    simp [he]

/-- Path-sum form of the lineage weights (Patterson et al. 2012): `weight X e` is the sum, over
the root-ward paths from `X` that traverse `e`, of the products of the admixture proportions
along the path. -/
theorem weight_eq_sum_paths (X : V) (e : G.Edge) :
    G.weight X e = ∑ π ∈ G.paths X, if e.1 ∈ π.zip π.tail then G.pathProb π else 0 := by
  induction X using G.wf.induction with
  | _ X ih =>
    rw [paths_eq]
    split_ifs with hX
    · have hc : e.1.1 ≠ X := by
        intro hc
        have he := e.2
        simp [hc, hX] at he
      rw [weight_eq]
      simp [hX, hc]
    · rw [Finset.sum_biUnion]
      · have hstep : ∀ Y ∈ G.parents X,
            (∑ π ∈ (G.paths Y).image (List.cons X),
              if e.1 ∈ π.zip π.tail then G.pathProb π else 0) =
                G.prop X Y * G.weight Y e +
                  if e.1 = (X, Y) then G.prop X Y else 0 := by
          intro Y hY
          rw [Finset.sum_image]
          · rw [Finset.sum_congr rfl (fun π hπ => path_edge_step G X Y hY e hπ),
              Finset.sum_add_distrib, ← Finset.mul_sum, ← ih Y hY]
            congr 1
            by_cases he : e.1 = (X, Y)
            · simp only [ite_eq_left he]
              rw [← Finset.mul_sum, sum_pathProb, mul_one]
            · simp [he]
          · intro a _ b _ h
            exact List.cons.inj h |>.2
        rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, sum_first_edge, weight_eq]
      · intro Y _ Z _ hYZ
        exact path_images_disjoint G X hYZ

/-- The graph is a tree: no node has two parents. -/
def IsTree : Prop := ∀ X, (G.parents X).card ≤ 1

/-- On a tree every visit probability is `0` or `1`. -/
theorem visit_eq_zero_or_one (hG : G.IsTree) (X c : V) :
    G.visit X c = 0 ∨ G.visit X c = 1 := by
  induction X using G.wf.induction with
  | _ X ih =>
    rw [visit_eq]
    split_ifs with hXc
    · exact Or.inr rfl
    · by_cases hX : X = G.root
      · simp [hX, G.parents_root]
      · have hcard : (G.parents X).card = 1 := by
          rcases G.card_parents X hX with h | h
          · exact h
          · have := hG X
            omega
        obtain ⟨Y, hY⟩ := Finset.card_eq_one.mp hcard
        have hp : G.prop X Y = 1 := by simpa [hY] using G.sum_prop X hX
        rw [hY, Finset.sum_singleton, hp, one_mul]
        exact ih Y (by simp [hY])

/-- On a tree every lineage weight is `0` or `1`. -/
theorem weight_eq_zero_or_one (hG : G.IsTree) (X : V) (e : G.Edge) :
    G.weight X e = 0 ∨ G.weight X e = 1 := by
  have hc : e.1.1 ≠ G.root := by
    intro h
    have he := e.2
    simp [h, G.parents_root] at he
  have hcard : (G.parents e.1.1).card = 1 := by
    rcases G.card_parents e.1.1 hc with h | h
    · exact h
    · have := hG e.1.1
      omega
  obtain ⟨Y, hY⟩ := Finset.card_eq_one.mp hcard
  have he : e.1.2 = Y := by simpa [hY] using e.2
  have hp : G.prop e.1.1 e.1.2 = 1 := by
    simpa [hY, he] using G.sum_prop e.1.1 hc
  simpa [weight, hp] using G.visit_eq_zero_or_one hG X e.1.1

/-! ### The induced drift model -/

variable [Fintype V] {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

/-- The drift model of an admixture graph: the populations are the nodes, the root frequency is
`root`, the edge increments are `incr` (square integrable and pairwise uncorrelated), the drift
length of an edge is the second moment of its increment, and the weights are the lineage
weights of the graph. -/
noncomputable def driftModel (root : Ω → ℝ) (incr : G.Edge → Ω → ℝ) (hroot : MemLp root 2 μ)
    (hincr : ∀ e, MemLp (incr e) 2 μ)
    (hinner : ∀ e f, e ≠ f → ∫ ω, incr e ω * incr f ω ∂μ = 0) : DriftModel μ G.Edge V where
  root := root
  incr := incr
  len e := ∫ ω, incr e ω ^ 2 ∂μ
  weight := G.weight
  memLp_root := hroot
  memLp_incr := hincr
  inner_incr := hinner
  sq_incr _ := rfl

/-- A tree-shaped admixture graph induces a drift model with binary loadings (all weights `0` or
`1`). -/
theorem hasBinaryLoadings_of_isTree (hG : G.IsTree) {M : DriftModel μ G.Edge V}
    (hM : M.weight = G.weight) : M.HasBinaryLoadings := by
  intro X e
  rw [hM]
  exact G.weight_eq_zero_or_one hG X e

/-- The three-population test on a tree-shaped admixture graph: `f3 C A B ≥ 0`. -/
theorem f3_nonneg_of_isTree (hG : G.IsTree) {M : DriftModel μ G.Edge V}
    (hM : M.weight = G.weight) (C A B : V) : 0 ≤ f3 μ M.freq C A B :=
  M.f3_nonneg_of_hasBinaryLoadings (G.hasBinaryLoadings_of_isTree hG hM) C A B

/-- The three-population statistic at an admixture node `X` with parents `A ≠ B`, proportions
`α = prop X A` and `β = prop X B` (`α + β = 1`), in a drift model with the graph's weights:
`f3 X A B = α² ℓ_{XA} + β² ℓ_{XB} - α β f2 A B`, where `ℓ_{XA}`, `ℓ_{XB}` are the drift
lengths of the two admixture edges. -/
theorem f3_admixture {M : DriftModel μ G.Edge V} (hM : M.weight = G.weight) {X A B : V}
    (hX : G.parents X = {A, B}) (hAB : A ≠ B) :
    f3 μ M.freq X A B =
      G.prop X A ^ 2 * M.len ⟨(X, A), by simp [hX]⟩ +
        G.prop X B ^ 2 * M.len ⟨(X, B), by simp [hX]⟩ -
        G.prop X A * G.prop X B * f2 μ M.freq A B := by
  have hXr : X ≠ G.root := by
    rintro rfl
    exact Finset.insert_ne_empty A {B} (hX.symm.trans G.parents_root)
  have hw := G.weight_admixture hX hAB
  have hsum := G.sum_prop X hXr
  rw [hX, Finset.sum_pair hAB] at hsum
  have h0 : ∀ Y ∈ G.parents X, ∀ e : G.Edge, e.1.1 = X → G.weight Y e = 0 :=
    fun Y hY e he => by rw [weight, he, G.visit_eq_zero_of_mem_parents hY, zero_mul]
  have hA0 := h0 A (by simp [hX])
  have hB0 := h0 B (by simp [hX])
  have key : ∀ e, (G.weight X e - G.weight A e) * (G.weight X e - G.weight B e) * M.len e =
      ((if e = ⟨(X, A), by simp [hX]⟩ then G.prop X A ^ 2 * M.len ⟨(X, A), by simp [hX]⟩
          else 0) +
        if e = ⟨(X, B), by simp [hX]⟩ then G.prop X B ^ 2 * M.len ⟨(X, B), by simp [hX]⟩
          else 0) -
        G.prop X A * G.prop X B * ((G.weight A e - G.weight B e) ^ 2 * M.len e) := by
    intro e
    by_cases he : e.1.1 = X
    · have hq := e.2
      rw [he, hX, Finset.mem_insert, Finset.mem_singleton] at hq
      have hwX : G.weight X e = G.prop X e.1.2 := by
        rw [hw]
        simp [hA0 e he, hB0 e he, he]
      rw [hwX, hA0 e he, hB0 e he]
      rcases hq with hq | hq
      · have : e = ⟨(X, A), by simp [hX]⟩ := Subtype.ext (Prod.ext he hq)
        subst this
        simp [hAB, sq]
      · have : e = ⟨(X, B), by simp [hX]⟩ := Subtype.ext (Prod.ext he hq)
        subst this
        simp [hAB.symm, sq]
    · have hne : ∀ Y (hY : Y ∈ G.parents X), e ≠ ⟨(X, Y), hY⟩ := fun Y hY h => he (by rw [h])
      rw [ite_eq_right (hne A _), ite_eq_right (hne B _), hw]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, he, ite_false]
      rw [show G.prop X B = 1 - G.prop X A by linarith]
      ring
  rw [M.f3_freq, M.f2_freq, hM, Finset.mul_sum]
  simp_rw [key, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp

/-- With no drift on the admixture edges, an admixture node `X` with parents `A ≠ B` and
proportion `α = prop X A` has `f3 X A B = -α (1 - α) f2 A B` (the hypothesis of the seed's
`DriftModel.f3_admixture`, here derived from the graph). -/
theorem f3_admixture_of_len_eq_zero {M : DriftModel μ G.Edge V} (hM : M.weight = G.weight)
    {X A B : V} (hX : G.parents X = {A, B}) (hAB : A ≠ B)
    (hA : M.len ⟨(X, A), by simp [hX]⟩ = 0) (hB : M.len ⟨(X, B), by simp [hX]⟩ = 0) :
    f3 μ M.freq X A B = -(G.prop X A * (1 - G.prop X A)) * f2 μ M.freq A B := by
  have hXr : X ≠ G.root := by
    rintro rfl
    exact Finset.insert_ne_empty A {B} (hX.symm.trans G.parents_root)
  have hsum := G.sum_prop X hXr
  rw [hX, Finset.sum_pair hAB] at hsum
  rw [G.f3_admixture hM hX hAB, hA, hB, show G.prop X B = 1 - G.prop X A by linarith]
  ring

end AdmixtureGraph

end MathlibExt.Biology.PopulationGenetics
