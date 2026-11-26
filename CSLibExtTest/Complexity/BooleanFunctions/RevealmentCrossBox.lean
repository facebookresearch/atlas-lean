/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.RevealmentCrossBox
public import CSLibExtTest.Complexity.BooleanFunctions.TreeComplete

/-!
# Tests for the box-crossing exploration tree

Tests for `CSLibExt.Complexity.BooleanFunctions.RevealmentCrossBox` on the path `0 — 1 — 2` and
the lattice edge `s₀ — s₁` of `ℤ¹` from the `RevealmentConstruction` tests:

* `reachOpen_symm` on the path; `cb_adj_coord_le_one`, `cb_not_mem_vertexBoundary` and
  `reachOpen_crosses` for the lattice edge (`k = 1`: the open edge leaves the box `[0, 0]` and
  reaches the boundary `{-1, 1}` of `[-1, 1]`);
* the two-set machine `xbGuard`, `xbStep` computed at small inputs (`decide`), and the run
  invariants `reach0Inv_runState`, `oSeedInv_runState`;
* non-vacuity of `eval_crossTree_iff` in both directions on the path (`o = 0`, `B = C = {2}`,
  `disc₀ = {2}`): `crossTree` answers `true` on the all-open configuration and `false` when the
  edge `1 — 2` is closed; `reveal_crossTree_le`;
* non-vacuity of `evalR_crossTree_connected` for the lattice edge with `k = n = 1`, where every
  hypothesis (adjacency, `o ∈ box 1 0`, the boundary `{-1, 1}` contained in `disc₀`, `o ∉ disc₀`)
  is proved and the tree has value `1` on the all-open configuration;
  `reveal_crossTree_le_connected`.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.Lattice StatMech.OSSS StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.TreeComplete

/-! ## Reachability and box coordinates -/

example : ReachOpen pathU pathV (fun _ => true) 2 0 := reachOpen_symm reachOpen_path_allOpen

example : (s₀ 0 - s₁ 0).natAbs ≤ 1 := cb_adj_coord_le_one 1 s₀ s₁ (latAdj ()) 0

/-- The origin lies in the box `[0, 0]`. -/
lemma s₀_mem_box : s₀ ∈ box 1 (1 - 1) := by simp [s₀]

/-- The site `1` lies outside the box `[0, 0]`. -/
lemma s₁_not_mem_box : s₁ ∉ box 1 (1 - 1) := by simp [s₁]

example : s₀ ∉ vertexBoundary 1 1 := cb_not_mem_vertexBoundary le_rfl s₀_mem_box

/-- `reachOpen_crosses`: the open edge `s₀ — s₁` crosses from the box `[0, 0]` to the boundary of
`[-1, 1]`. -/
example : ConnOpenSet (fun _ : Unit => s₀) (fun _ => s₁) (fun _ => true) s₀ (vertexBoundary 1 1) :=
  reachOpen_crosses le_rfl latAdj reachOpen_lat s₀_mem_box s₁_not_mem_box

/-! ## The two-set machine on the path -/

example : xbGuard pathU pathV (({2}, ∅) : XState (Fin 3)) false = true := by decide
example : xbStep pathU pathV 0 (({2}, ∅) : XState (Fin 3)) false true = ({1, 2}, ∅) := by decide
example : xbStep pathU pathV 0 (({1, 2}, ∅) : XState (Fin 3)) true true = ({0, 1, 2}, {0}) := by
  decide
example : xbStep pathU pathV 0 (({0, 1, 2}, {0}) : XState (Fin 3)) true true
    = ({0, 1, 2}, {0, 1}) := by decide

example (ω : ConfigSpace Bool) : oSeedInv (0 : Fin 3)
    (runState (xbGuard pathU pathV) (xbStep pathU pathV 0) ω [false, true] ({2}, ∅)) :=
  oSeedInv_runState pathU pathV 0 ω _ _ (by simp [oSeedInv])

example (ω : ConfigSpace Bool) : reach0Inv pathU pathV ω (0 : Fin 3)
    (runState (xbGuard pathU pathV) (xbStep pathU pathV 0) ω [false, true] ({2}, ∅)) :=
  reach0Inv_runState pathU pathV ω 0 _ _ (by simp [reach0Inv])

/-! ## The box-crossing tree on the path -/

/-- The box-crossing tree of the path from `disc₀ = {2}` towards `o = 0`, with target `C = {2}`. -/
noncomputable def pathCross : DecisionTree Bool := crossTree pathU pathV 0 {2} [false, true] {2}

/-- `eval_crossTree_iff` for the path: `pathCross` decides whether `0` is connected to `{2}`. -/
lemma pathCross_iff (ω : ConfigSpace Bool) :
    pathCross.eval ω = true ↔ ConnOpenSet pathU pathV ω 0 {2} :=
  eval_crossTree_iff pathU pathV 0 {2} {2} _ path_mem_list {2} path_B_sub (by decide)
    (fun _ h => h) ω

example : pathCross.eval (fun _ => true) = true := (pathCross_iff _).2 connOpenSet_path_allOpen

example : pathCross.eval (fun b => b) = false := by
  rw [← Bool.not_eq_true, pathCross_iff]; exact not_connOpenSet_path_id

open scoped Classical in
example : reveal νHalf pathCross true
    ≤ expect νHalf (fun ω => if ConnOpenSet pathU pathV ω 0 {2} then (1 : ℝ) else 0)
      + expect νHalf (fun ω => if ConnOpenSet pathU pathV ω 1 {2} then (1 : ℝ) else 0) :=
  reveal_crossTree_le νHalf_isProbWeight pathU pathV 0 {2} {2} _ {2} path_disc_sub true

/-! ## The box-crossing tree for the lattice edge -/

/-- The site `-1` of `ℤ¹`. -/
def sNeg : Site 1 := fun _ => -1

/-- The boundary of `[-1, 1]` in `ℤ¹` is `{-1, 1}`. -/
lemma mem_vertexBoundary_one (b : Site 1) (hb : b ∈ vertexBoundary 1 1) :
    b ∈ ({s₁, sNeg} : Finset (Site 1)) := by
  simp only [mem_vertexBoundary, mem_box, Nat.sub_self, not_forall] at hb
  obtain ⟨h1, i, hi⟩ := hb
  have h0 : i = 0 := Subsingleton.elim i 0
  subst h0
  have hb0 : b 0 = 1 ∨ b 0 = -1 := by have := h1 0; omega
  rw [Finset.mem_insert, Finset.mem_singleton]
  rcases hb0 with h | h
  · exact Or.inl (funext fun j => by rw [Subsingleton.elim j 0, h]; rfl)
  · exact Or.inr (funext fun j => by rw [Subsingleton.elim j 0, h]; rfl)

/-- The origin is not in the boundary set `{1, -1}`. -/
lemma s₀_not_mem_disc : s₀ ∉ ({s₁, sNeg} : Finset (Site 1)) := by
  simp [s₀, s₁, sNeg, funext_iff]

open scoped Classical in
/-- `evalR_crossTree_connected` for the lattice edge: the crossing tree has value `1` on the
all-open configuration. -/
example : (crossTree (fun _ : Unit => s₀) (fun _ => s₁) s₀ (vertexBoundary 1 1) [()]
    {s₁, sNeg}).evalR (fun _ => true) = 1 := by
  have hc : ConnectedToSet 1 (liftCfg latEdge (fun _ => true)) s₀ (vertexBoundary 1 1) :=
    connOpenSet_imp_connectedToSet latEdge_injective latEdge_coh latAdj
      (reachOpen_crosses le_rfl latAdj reachOpen_lat s₀_mem_box s₁_not_mem_box)
  rw [evalR_crossTree_connected latEdge_injective latEdge_coh latAdj 1 1 le_rfl le_rfl s₀
    s₀_mem_box [()] (fun _ => List.mem_singleton_self ()) {s₁, sNeg} mem_vertexBoundary_one
    s₀_not_mem_disc]
  simp only [hc, ↓reduceIte]

open scoped Classical in
example : reveal νUnit (crossTree (fun _ : Unit => s₀) (fun _ => s₁) s₀ (vertexBoundary 1 1) [()]
      {s₁, sNeg}) ()
    ≤ expect νUnit (fun ω =>
        if ConnectedToSet 1 (liftCfg latEdge ω) s₀ (vertexBoundary 1 1) then (1 : ℝ) else 0)
      + expect νUnit (fun ω =>
        if ConnectedToSet 1 (liftCfg latEdge ω) s₁ (vertexBoundary 1 1) then (1 : ℝ) else 0) :=
  reveal_crossTree_le_connected νUnit_isProbWeight latEdge_injective latEdge_coh latAdj s₀ _ 1
    [()] {s₁, sNeg} (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [s₁, sNeg]) ()

end StatMechTest.BooleanFunctions
