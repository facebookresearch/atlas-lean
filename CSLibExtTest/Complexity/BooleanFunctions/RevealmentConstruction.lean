/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.RevealmentConstruction
public import CSLibExtTest.Complexity.BooleanFunctions.OSSS

/-!
# Tests for decision trees from state machines and the exploration tree

Tests for `CSLibExt.Complexity.BooleanFunctions.RevealmentConstruction` on two small graphs:

* the path `0 — 1 — 2` on `Fin 3` with edge set `Bool` (`true` is the edge `0 — 1`, `false` the
  edge `1 — 2`), endpoint maps `pathU`, `pathV`;
* the one-edge subgraph `s₀ — s₁` of the lattice `ℤ¹` (`d = 1`), with edge set `Unit`.

What is tested:

* `buildTree`, `runState`, `geomGuard`, `geomStep` and `exploreTree` computed at small inputs:
  exploring the path from `2` along `[false, true]` gives the `AND` tree of the two edges;
  `eval_buildTree` and `runState_inv` (with `geomInv`);
* `ReachOpen` and `ConnOpenSet` on the path: `0` reaches `2` when both edges are open and only
  itself when every edge is closed;
* `eval_exploreTree_imp_conn` and `queried_exploreTree_imp` on the path;
  `reveal_exploreTree_le` with the revealment computed exactly (`1/2` for the edge `0 — 1`);
* the lattice instance: `liftCfg_apply_edge`, `reachOpen_imp_connected`,
  `connOpenSet_imp_connectedToSet` and `reveal_exploreTree_le_connected`, with the hypotheses
  (injectivity, coherence, lattice adjacency) discharged for the edge `s₀ — s₁`.

The path and lattice data are reused by the tests of `TreeComplete` and `RevealmentCrossBox`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.Lattice StatMech.OSSS StatMech.OSSS.RevealmentConstruction

/-! ## The path `0 — 1 — 2` -/

/-- First endpoint of the path edges: `true ↦ 0`, `false ↦ 1`. -/
def pathU (b : Bool) : Fin 3 := if b then 0 else 1

/-- Second endpoint of the path edges: `true ↦ 1`, `false ↦ 2`. -/
def pathV (b : Bool) : Fin 3 := if b then 1 else 2

/-- The exploration tree of the path from the target `2`, scanning the edges `[false, true]` and
answering whether `0` was discovered. -/
def pathTree : DecisionTree Bool :=
  exploreTree pathU pathV (fun disc => decide ((0 : Fin 3) ∈ disc)) [false, true] {2}

example : geomGuard pathU pathV {2} true = false := by decide
example : geomGuard pathU pathV {2} false = true := by decide
example : geomStep pathU pathV {2} false true = {1, 2} := by decide
example : geomStep pathU pathV {2} false false = {2} := by decide

/-- Exploring the path from `2` gives the `AND` tree of the edges `false` and `true`. -/
lemma pathTree_eq : pathTree = .node false (.node true (.leaf true) (.leaf false)) (.leaf false) :=
  rfl

example : runState (geomGuard pathU pathV) (geomStep pathU pathV) (fun _ => true) [false, true] {2}
    = {0, 1, 2} := by decide

example : pathTree.eval (fun _ => true) = true := by decide
example : pathTree.eval (fun b => b) = false := by decide

example (ω : ConfigSpace Bool) : pathTree.eval ω
    = decide ((0 : Fin 3) ∈ runState (geomGuard pathU pathV) (geomStep pathU pathV) ω
        [false, true] {2}) :=
  eval_buildTree _ _ _ ω _ _

/-- Both edges open: `0` reaches `2`. -/
lemma reachOpen_path_allOpen : ReachOpen pathU pathV (fun _ => true) 0 2 :=
  .step true rfl (Or.inl ⟨rfl, rfl⟩) (.step false rfl (Or.inl ⟨rfl, rfl⟩) (.refl 2))

/-- Both edges open: `0` is connected to `{2}`. -/
lemma connOpenSet_path_allOpen : ConnOpenSet pathU pathV (fun _ => true) 0 {2} :=
  ⟨2, rfl, reachOpen_path_allOpen⟩

/-- With every edge closed, a vertex reaches only itself. -/
lemma eq_of_reachOpen_allClosed {endU endV : Bool → Fin 3} {x y : Fin 3}
    (h : ReachOpen endU endV (fun _ => false) x y) : x = y := by
  induction h with
  | refl => rfl
  | step _ hopen => exact absurd hopen Bool.false_ne_true

example : ¬ ConnOpenSet pathU pathV (fun _ => false) 0 {2} := by
  rintro ⟨b, hb, h⟩
  rw [Set.mem_singleton_iff] at hb
  subst hb
  exact absurd (eq_of_reachOpen_allClosed h) (by decide)

example (ω : ConfigSpace Bool) : geomInv pathU pathV ω {2}
    (runState (geomGuard pathU pathV) (geomStep pathU pathV) ω [false, true] {2}) :=
  runState_inv _ _ _ ω (fun σ e hσ hg => geomInv_step pathU pathV ω {2} σ e hσ hg) _ _
    (fun x hx => connOpenSet_of_mem (by simpa using hx))

/-- `eval_exploreTree_imp_conn`: the tree answers `true` on the all-open configuration, so `0` is
connected to `2`. -/
example : ConnOpenSet pathU pathV (fun _ => true) 0 {2} :=
  eval_exploreTree_imp_conn pathU pathV 0 {2} [false, true] {2} (fun x hx => by simpa using hx)
    (fun _ => true) (by decide)

example (ω : ConfigSpace Bool) (i : Bool) (hi : i ∈ pathTree.queried ω) :
    ConnOpenSet pathU pathV ω (pathU i) {2} ∨ ConnOpenSet pathU pathV ω (pathV i) {2} :=
  queried_exploreTree_imp pathU pathV _ ω {2} [false, true] {2} (fun x hx => by simpa using hx)
    i hi

/-- The edge `0 — 1` is queried exactly when the edge `1 — 2` is open: revealment `1/2`. -/
lemma reveal_pathTree_true : reveal νHalf pathTree true = 1 / 2 := by
  rw [pathTree_eq]
  simp [reveal, expect, weight, sum_configSpace_bool, DecisionTree.queried, bernoulliWeight]
  norm_num

open scoped Classical in
/-- `reveal_exploreTree_le` for the path and the edge `0 — 1`. -/
example : (1 / 2 : ℝ)
    ≤ expect νHalf (fun ω => if ConnOpenSet pathU pathV ω 0 {2} then (1 : ℝ) else 0)
      + expect νHalf (fun ω => if ConnOpenSet pathU pathV ω 1 {2} then (1 : ℝ) else 0) := by
  have h := reveal_exploreTree_le νHalf_isProbWeight pathU pathV
    (fun disc => decide ((0 : Fin 3) ∈ disc)) {2} [false, true] {2}
    (fun x hx => by simpa using hx) true
  rwa [← pathTree, reveal_pathTree_true] at h

/-! ## One edge of the lattice `ℤ¹` -/

/-- The origin of `ℤ¹`. -/
def s₀ : Site 1 := fun _ => 0

/-- The site `1` of `ℤ¹`. -/
def s₁ : Site 1 := fun _ => 1

/-- The single lattice edge `s₀ — s₁`. -/
def latEdge : Unit → Sym2 (Site 1) := fun _ => s(s₀, s₁)

/-- `latEdge` is injective (its domain is `Unit`). -/
lemma latEdge_injective : Function.Injective latEdge := fun _ _ _ => rfl

/-- `latEdge` is coherent with the endpoint maps `s₀`, `s₁`. -/
lemma latEdge_coh : ∀ e, latEdge e = s((fun _ => s₀) e, (fun _ => s₁) e) := fun _ => rfl

/-- `s₀` and `s₁` are adjacent in the lattice `ℤ¹`. -/
lemma latAdj : ∀ _ : Unit, (hypercubicLattice 1).Adj s₀ s₁ := fun _ => by
  rw [hypercubicLattice_adj]; simp [s₀, s₁]

example : liftCfg latEdge (fun _ => true) s(s₀, s₁) = true :=
  liftCfg_apply_edge latEdge_injective _ ()

/-- The open edge `s₀ — s₁` as an abstract open path. -/
lemma reachOpen_lat : ReachOpen (fun _ : Unit => s₀) (fun _ => s₁) (fun _ => true) s₀ s₁ :=
  .step () rfl (Or.inl ⟨rfl, rfl⟩) (.refl s₁)

/-- `reachOpen_imp_connected`: the lifted configuration connects `s₀` to `s₁`. -/
example : Connected 1 (liftCfg latEdge (fun _ => true)) s₀ s₁ :=
  reachOpen_imp_connected latEdge_injective latEdge_coh latAdj reachOpen_lat

example : ConnectedToSet 1 (liftCfg latEdge (fun _ => true)) s₀ {s₁} :=
  connOpenSet_imp_connectedToSet latEdge_injective latEdge_coh latAdj ⟨s₁, rfl, reachOpen_lat⟩

/-- The Bernoulli(`1/2`) weight on the one-edge set `Unit`. -/
noncomputable abbrev νUnit : Unit → Bool → ℝ := bernoulliWeight (1 / 2)

/-- `νUnit` is a probability weight. -/
lemma νUnit_isProbWeight : IsProbWeight νUnit :=
  bernoulliWeight_isProbWeight (by norm_num) (by norm_num)

open scoped Classical in
example : reveal νUnit (exploreTree (fun _ : Unit => s₀) (fun _ => s₁)
      (fun disc => decide (s₀ ∈ disc)) [()] {s₁}) ()
    ≤ expect νUnit (fun ω => if ConnectedToSet 1 (liftCfg latEdge ω) s₀ {s₁} then (1 : ℝ) else 0)
      + expect νUnit
          (fun ω => if ConnectedToSet 1 (liftCfg latEdge ω) s₁ {s₁} then (1 : ℝ) else 0) :=
  reveal_exploreTree_le_connected νUnit_isProbWeight latEdge_injective latEdge_coh latAdj _ {s₁}
    [()] {s₁} (fun x hx => by simpa using hx) ()

end StatMechTest.BooleanFunctions
