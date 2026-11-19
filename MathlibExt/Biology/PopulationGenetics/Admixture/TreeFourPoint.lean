/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.AdmixtureGraph
public import MathlibExt.Biology.Phylogenetics.Buneman

/-!
# Tree-shaped admixture graphs give tree metrics

On a tree-shaped admixture graph (`AdmixtureGraph.IsTree`: no admixture node) every non-root
node has a single parent, taken with proportion `1`, so the lineage of `X` is the root-ward
path from `X`: `visit X c = 1` exactly when `c` is `X` or an ancestor of `X`, and
`weight X e = visit X c` for the child endpoint `c` of `e`. Two nodes on one root-ward path
are comparable, so lineage edge sets are laminar: two edges on a common lineage are traversed
by nested sets of populations.

For populations `x, y, z, t`, call an edge an `xz | yt` edge when exactly the lineages of
`x` and `z`, or exactly those of `y` and `t`, traverse it, and an `xt | yz` edge likewise.
Laminarity rules out having edges of both kinds. Since the differences of the quartet pair
sums of `f2` are `2 ∑ e, (w x e - w t e) (w y e - w z e) len e` and
`2 ∑ e, (w x e - w z e) (w y e - w t e) len e`, whose summands are negative exactly on the
`xz | yt` and on the `xt | yz` edges, one of the two differences is nonnegative: this is the
four-point condition.

## Main results

* `AdmixtureGraph.visit_eq_one_iff_reflTransGen_of_isTree`: on a tree the lineage of `X`
  passes through `c` iff `c` is `X` or an ancestor of `X`.
* `AdmixtureGraph.visit_trans_of_isTree`, `AdmixtureGraph.visit_chain_of_isTree`: on a tree,
  `visit · · = 1` is transitive, and two nodes on one lineage are comparable.
* `AdmixtureGraph.weight_eq_visit_of_isTree`: on a tree `weight X e = visit X c` for the
  child endpoint `c` of `e`.
* `AdmixtureGraph.weight_laminar_of_isTree`: two edges on a common lineage are traversed by
  nested sets of populations.
* `AdmixtureGraph.quartet_compatible_of_isTree`: no tree has both `xz | yt` and `xt | yz`
  edges.
* `AdmixtureGraph.fourPointCondition_f2_of_isTree`: in a drift model with the weights of a
  tree-shaped admixture graph, `f2` satisfies the four-point condition, and
  `AdmixtureGraph.isTreeMetric_f2_of_isTree`: by Buneman's theorem `f2` is a tree metric.
-/

@[expose] public section

open MeasureTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.Phylogenetics.Buneman

namespace MathlibExt.Biology.PopulationGenetics

namespace AdmixtureGraph

variable {V : Type*} [DecidableEq V] (G : AdmixtureGraph V)

/-! ### Lineages on a tree -/

omit [DecidableEq V] in
/-- On a tree every non-root node has exactly one parent. -/
theorem exists_parents_eq_singleton_of_isTree (hG : G.IsTree) {X : V} (hX : X ≠ G.root) :
    ∃ Y, G.parents X = {Y} := by
  apply Finset.card_eq_one.mp
  rcases G.card_parents X hX with h | h
  · exact h
  · have := hG X
    omega

omit [DecidableEq V] in
/-- On a tree a parent of `X` is its only parent. -/
theorem parents_eq_singleton_of_mem_of_isTree (hG : G.IsTree) {X Y : V}
    (hY : Y ∈ G.parents X) : G.parents X = {Y} :=
  Finset.eq_singleton_iff_unique_mem.mpr
    ⟨hY, fun Z hZ => Finset.card_le_one.mp (hG X) Z hZ Y hY⟩

/-- If `Y` is the only parent of `X ≠ c`, the lineage of `X` passes through `c` iff the
lineage of `Y` does. -/
theorem visit_eq_visit_of_parents_eq_singleton {X Y c : V} (hY : G.parents X = {Y})
    (hXc : X ≠ c) : G.visit X c = G.visit Y c := by
  have hXr : X ≠ G.root := by
    rintro rfl
    simp [G.parents_root] at hY
  have hp : G.prop X Y = 1 := by simpa [hY] using G.sum_prop X hXr
  rw [G.visit_eq X c, ite_eq_right hXc, hY, Finset.sum_singleton, hp, one_mul]

/-- The root's lineage passes through no other node. -/
theorem visit_root_left {c : V} (hc : G.root ≠ c) : G.visit G.root c = 0 := by
  rw [G.visit_eq, ite_eq_right hc, G.parents_root, Finset.sum_empty]

/-- On a tree the lineage of `X` passes through `c` exactly when `c` is `X` or an ancestor of
`X` (reached from `X` by repeatedly passing to the parent). -/
theorem visit_eq_one_iff_reflTransGen_of_isTree (hG : G.IsTree) {X c : V} :
    G.visit X c = 1 ↔ Relation.ReflTransGen (fun a b => a ∈ G.parents b) c X := by
  constructor
  · intro h
    induction X using G.wf.induction with
    | _ X ih =>
      by_cases hXc : X = c
      · subst hXc
        exact Relation.ReflTransGen.refl
      by_cases hXr : X = G.root
      · subst hXr
        rw [G.visit_root_left hXc] at h
        exact absurd h zero_ne_one
      obtain ⟨Y, hY⟩ := G.exists_parents_eq_singleton_of_isTree hG hXr
      rw [G.visit_eq_visit_of_parents_eq_singleton hY hXc] at h
      exact Relation.ReflTransGen.tail (ih Y (by simp [hY]) h) (by simp [hY])
  · intro h
    induction h with
    | refl => exact G.visit_self c
    | @tail Y X _ hYX ih =>
      by_cases hXc : X = c
      · subst hXc
        exact G.visit_self X
      rw [G.visit_eq_visit_of_parents_eq_singleton
        (G.parents_eq_singleton_of_mem_of_isTree hG hYX) hXc]
      exact ih

/-- On a tree `visit · · = 1` is transitive: if the lineage of `X` passes through `c` and the
lineage of `c` passes through `d`, then the lineage of `X` passes through `d`. -/
theorem visit_trans_of_isTree (hG : G.IsTree) {X c d : V} (h₁ : G.visit X c = 1)
    (h₂ : G.visit c d = 1) : G.visit X d = 1 := by
  induction X using G.wf.induction with
  | _ X ih =>
    by_cases hXc : X = c
    · subst hXc
      exact h₂
    by_cases hXr : X = G.root
    · subst hXr
      rw [G.visit_root_left hXc] at h₁
      exact absurd h₁ zero_ne_one
    obtain ⟨Y, hY⟩ := G.exists_parents_eq_singleton_of_isTree hG hXr
    rw [G.visit_eq_visit_of_parents_eq_singleton hY hXc] at h₁
    by_cases hXd : X = d
    · subst hXd
      exact G.visit_self X
    rw [G.visit_eq_visit_of_parents_eq_singleton hY hXd]
    exact ih Y (by simp [hY]) h₁

/-- On a tree two nodes on the lineage of `X` are comparable: one lies on the lineage of the
other. -/
theorem visit_chain_of_isTree (hG : G.IsTree) {X c d : V} (hc : G.visit X c = 1)
    (hd : G.visit X d = 1) : G.visit c d = 1 ∨ G.visit d c = 1 := by
  induction X using G.wf.induction with
  | _ X ih =>
    by_cases hXc : X = c
    · subst hXc
      exact Or.inl hd
    by_cases hXd : X = d
    · subst hXd
      exact Or.inr hc
    by_cases hXr : X = G.root
    · subst hXr
      rw [G.visit_root_left hXc] at hc
      exact absurd hc zero_ne_one
    obtain ⟨Y, hY⟩ := G.exists_parents_eq_singleton_of_isTree hG hXr
    rw [G.visit_eq_visit_of_parents_eq_singleton hY hXc] at hc
    rw [G.visit_eq_visit_of_parents_eq_singleton hY hXd] at hd
    exact ih Y (by simp [hY]) hc hd

/-- On a tree the lineage of `X` traverses the edge `e = (c, p)` exactly when it passes
through the child endpoint `c`: `weight X e = visit X c`. -/
theorem weight_eq_visit_of_isTree (hG : G.IsTree) (X : V) (e : G.Edge) :
    G.weight X e = G.visit X e.1.1 := by
  have hc : e.1.1 ≠ G.root := by
    intro h
    have he := e.2
    simp [h, G.parents_root] at he
  obtain ⟨Y, hY⟩ := G.exists_parents_eq_singleton_of_isTree hG hc
  have he : e.1.2 = Y := by simpa [hY] using e.2
  have hp : G.prop e.1.1 e.1.2 = 1 := by simpa [hY, he] using G.sum_prop e.1.1 hc
  rw [weight, hp, mul_one]

/-- Lineage edges on a tree are laminar: if the lineage of `X` traverses both `e` and `f`,
then every lineage through one of them also traverses the other one. -/
theorem weight_laminar_of_isTree (hG : G.IsTree) {X : V} {e f : G.Edge}
    (he : G.weight X e = 1) (hf : G.weight X f = 1) :
    (∀ Y, G.weight Y e = 1 → G.weight Y f = 1) ∨
      ∀ Y, G.weight Y f = 1 → G.weight Y e = 1 := by
  simp only [G.weight_eq_visit_of_isTree hG] at he hf ⊢
  rcases G.visit_chain_of_isTree hG he hf with h | h
  · exact Or.inl fun Y hY => G.visit_trans_of_isTree hG hY h
  · exact Or.inr fun Y hY => G.visit_trans_of_isTree hG hY h

/-! ### Quartets -/

/-- A product `(a - d) (b - c)` of differences of `0`/`1` values is negative only at
`(a, b, c, d) = (1, 0, 1, 0)` and `(0, 1, 0, 1)`. -/
private theorem binary_pattern {a b c d : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1)
    (hc : c = 0 ∨ c = 1) (hd : d = 0 ∨ d = 1) (h : (a - d) * (b - c) < 0) :
    (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 0) ∨ (a = 0 ∧ b = 1 ∧ c = 0 ∧ d = 1) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> norm_num at h <;> norm_num

/-- Quartet compatibility on a tree: either no edge is an `xz | yt` edge (traversed by exactly
the lineages of `x` and `z`, or exactly those of `y` and `t`), or no edge is an `xt | yz`
edge. In product form, the summands of one of the two quartet differences of `f2` are all
nonnegative. -/
theorem quartet_compatible_of_isTree (hG : G.IsTree) (x y z t : V) :
    (∀ e, 0 ≤ (G.weight x e - G.weight t e) * (G.weight y e - G.weight z e)) ∨
      ∀ e, 0 ≤ (G.weight x e - G.weight z e) * (G.weight y e - G.weight t e) := by
  rw [or_iff_not_imp_left]
  intro hne f
  by_contra hf
  rw [not_le] at hf
  obtain ⟨e, he⟩ := not_forall.mp hne
  rw [not_le] at he
  have hb := G.weight_eq_zero_or_one hG
  -- two edges on a common lineage cannot each separate a population from the other edge
  have key : ∀ {X Y Z : V}, G.weight X e = 1 → G.weight X f = 1 → G.weight Y e = 1 →
      G.weight Y f = 0 → G.weight Z f = 1 → G.weight Z e = 0 → False := by
    intro X Y Z hXe hXf hYe hYf hZf hZe
    rcases G.weight_laminar_of_isTree hG hXe hXf with h | h
    · linarith [h Y hYe]
    · linarith [h Z hZf]
  obtain ⟨hxe, hye, hze, hte⟩ | ⟨hxe, hye, hze, hte⟩ :=
    binary_pattern (hb x e) (hb y e) (hb z e) (hb t e) he <;>
  obtain ⟨hxf, hyf, htf, hzf⟩ | ⟨hxf, hyf, htf, hzf⟩ :=
    binary_pattern (hb x f) (hb y f) (hb t f) (hb z f) hf
  · exact key hxe hxf hze hzf htf hte
  · exact key hze hzf hxe hxf hyf hye
  · exact key hte htf hye hyf hxf hxe
  · exact key hye hyf hte htf hzf hze

end AdmixtureGraph

/-! ### The four-point condition -/

/-- In a drift model carrying the weights of a tree-shaped admixture graph, `f2` satisfies the
four-point condition. Binary loadings alone do not suffice: the square weights `00, 10, 01,
11` are binary but their `f2` violates it. Here the lineages are root-ward paths of one tree,
so for each quartet the edges cannot separate it in two different ways
(`AdmixtureGraph.quartet_compatible_of_isTree`). -/
theorem AdmixtureGraph.fourPointCondition_f2_of_isTree {V Ω : Type*} [DecidableEq V]
    [Fintype V] {m : MeasurableSpace Ω} {μ : Measure Ω} (G : AdmixtureGraph V)
    (hG : G.IsTree) {M : DriftModel μ G.Edge V} (hM : M.weight = G.weight) :
    MathlibExt.Biology.Phylogenetics.Buneman.FourPointCondition (f2 μ M.freq) := by
  have key : ∀ A B C D : V, f2 μ M.freq A C + f2 μ M.freq B D -
      (f2 μ M.freq A B + f2 μ M.freq C D) =
        2 * ∑ e, (G.weight A e - G.weight D e) * (G.weight B e - G.weight C e) * M.len e := by
    intro A B C D
    simp only [M.f2_freq, hM, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  intro x y z t
  rcases G.quartet_compatible_of_isTree hG x y z t with h | h
  · have h0 : 0 ≤ ∑ e, (G.weight x e - G.weight t e) * (G.weight y e - G.weight z e) *
        M.len e := Finset.sum_nonneg fun e _ => mul_nonneg (h e) (M.len_nonneg e)
    have := key x y z t
    exact le_max_of_le_left (by linarith)
  · have h0 : 0 ≤ ∑ e, (G.weight x e - G.weight z e) * (G.weight y e - G.weight t e) *
        M.len e := Finset.sum_nonneg fun e _ => mul_nonneg (h e) (M.len_nonneg e)
    have := key x y t z
    exact le_max_of_le_right (by linarith [f2_comm (μ := μ) (p := M.freq) t z])

/-- In a drift model carrying the weights of a tree-shaped admixture graph, `f2` is a tree
metric: `fourPointCondition_f2_of_isTree` and Buneman's theorem
(`isTreeMetric_of_fourPointCondition`, with `f2_self` and `f2_comm`). -/
theorem AdmixtureGraph.isTreeMetric_f2_of_isTree {V Ω : Type*} [DecidableEq V]
    [Fintype V] {m : MeasurableSpace Ω} {μ : Measure Ω} (G : AdmixtureGraph V)
    (hG : G.IsTree) {M : DriftModel μ G.Edge V} (hM : M.weight = G.weight) :
    IsTreeMetric (f2 μ M.freq) :=
  isTreeMetric_of_fourPointCondition _ (fun _ => f2_self _) (fun _ _ => f2_comm _ _)
    (G.fourPointCondition_f2_of_isTree hG hM)

end MathlibExt.Biology.PopulationGenetics
