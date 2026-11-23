/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.CSP.TreeCSP
public meta import CSLibExt.Algorithms.Lean.CSP.TreeCSP
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Pi
public meta import Mathlib.Data.Fintype.Pi
public meta import Mathlib.Data.Finset.Max

/-!
# Tree-CSP tests

Closed checks, by `decide`, on four fixtures:

* a path `0 - 1 - 2 - 3` with `x < y` along each edge and domains `0..3`: the DAC pass prunes
  the root to `{0}` and `treeSolve` returns `0, 1, 2, 3`; the theorems certify solvability;
* a star with centre `0`, leaves `1, 2, 3`, `≠` constraints and leaf domains `{0}`, `{1}`,
  `{2, 3}`: greedy without DAC picks `0` for the centre and fails at leaf `1` (backtracking
  would be needed); after the DAC pass the centre's domain is `{2, 3}` and `treeSolve` succeeds;
* an unsolvable path `0 - 1 - 2` with `x < y` over two values: the DAC pass empties the root's
  domain, `treeSolve` returns `none`, and `treeSolve_ne_none_iff` proves there is no solution;
* the cycle counterexample: three pairwise-different variables with two colours. Every arc is
  consistent and greedy along the spanning path `0 - 1 - 2` returns `0, 1, 0`, which violates
  the closing arc `(0, 2)`; no solution exists and the arcs are not tree arcs, so the tree
  hypothesis cannot be dropped.

An executed fixture runs `treeSolve` on 60 pseudo-random path, star and tree CSPs and compares
it with brute force: it succeeds iff a solution exists, returns a solution, and the DAC pass
stays within `n · d²` checks.
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.Lean.CSP.TreeCSP

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.ArcConsistency

/-- Both orientations of each edge `(x, y)`; `rel a b` constrains `x = a` with `y = b`. -/
def edgeCSP {n k : ℕ} (edges : List (Fin n × Fin n)) (rel : Fin k → Fin k → Bool) :
    BinaryCSP (Fin n) (Fin k) :=
  ⟨edges.flatMap fun e => [e, (e.2, e.1)], fun x y a b =>
    if (x, y) ∈ edges then rel a b else if (y, x) ∈ edges then rel b a else true⟩

/-- Select the least member. -/
def minSel {k : ℕ} (s : Finset (Fin k)) : Option (Fin k) := s.min

theorem isSelector_minSel (k : ℕ) : IsSelector (minSel (k := k)) :=
  ⟨fun _ _ h => Finset.mem_of_min h, fun _ hs h => hs.ne_empty (Finset.min_eq_top.1 h)⟩

/-! ## Path `0 - 1 - 2 - 3`, increasing -/

/-- `x < y` along each edge of the path `0 - 1 - 2 - 3`. -/
def pathCSP : BinaryCSP (Fin 4) (Fin 4) := edgeCSP [(0, 1), (1, 2), (2, 3)] fun a b => a < b

/-- The path rooted at `0`. -/
def pathParent : Fin 4 → Option (Fin 4) := ![none, some 0, some 1, some 2]

theorem pathOrder : RootedOrder pathParent [0, 1, 2, 3] :=
  ⟨by decide, by decide, by decide, by decide⟩
theorem pathSym : ArcConsistency.Symmetric pathCSP := by unfold ArcConsistency.Symmetric; decide
theorem pathTree : IsTreeArcs pathCSP pathParent := by unfold IsTreeArcs; decide
theorem pathEdge : ∀ x p, pathParent x = some p → (p, x) ∈ pathCSP.arcs := by decide

example : (dac pathCSP pathParent [0, 1, 2, 3] fun _ => Finset.univ).ret 0 = {0} := by decide
example : (dac pathCSP pathParent [0, 1, 2, 3] fun _ => Finset.univ).time = 4 * 4 + 3 * 4 + 2 * 4
    := by decide
example : treeSolve pathCSP pathParent [0, 1, 2, 3] minSel (fun _ => Finset.univ) =
    some ![0, 1, 2, 3] := by decide

/-- The theorems certify a solution from the run. -/
example : ∃ σ, IsSolution pathCSP (fun _ => Finset.univ) σ :=
  (treeSolve_ne_none_iff (isSelector_minSel 4) pathOrder pathSym pathTree pathEdge _).1
    (by decide)

/-- The cost bound at `n = 4`, `d = 4`. -/
example : (dac pathCSP pathParent [0, 1, 2, 3] fun _ => Finset.univ).time ≤ 4 * (4 * 4) :=
  dac_time_le 4 (fun _ => Finset.univ) fun _ => by rw [Finset.card_univ, Fintype.card_fin]

/-- The same bound, counted by the number of variables. -/
example : (dac pathCSP pathParent [0, 1, 2, 3] fun _ => Finset.univ).time ≤
    Fintype.card (Fin 4) * (4 * 4) :=
  dac_time_le_card pathOrder 4 (fun _ => Finset.univ) fun _ => by
    rw [Finset.card_univ, Fintype.card_fin]

/-- A repeated variable is not a rooted order: the cost bound counts each variable once. -/
example : ¬RootedOrder pathParent [0, 1, 1, 2, 3] := by
  intro h
  exact (by decide : ¬List.Nodup ([0, 1, 1, 2, 3] : List (Fin 4))) h.nodup

/-! ## Star: DAC is what makes greedy backtrack-free -/

/-- `≠` between the centre `0` and each leaf `1, 2, 3`. -/
def starCSP : BinaryCSP (Fin 4) (Fin 4) := edgeCSP [(0, 1), (0, 2), (0, 3)] fun a b => a ≠ b

/-- The star rooted at its centre. -/
def starParent : Fin 4 → Option (Fin 4) := ![none, some 0, some 0, some 0]

/-- Full centre domain; leaf domains `{0}`, `{1}`, `{2, 3}`. -/
def starDom : Fin 4 → Finset (Fin 4) := ![Finset.univ, {0}, {1}, {2, 3}]

theorem starOrder : RootedOrder starParent [0, 1, 2, 3] :=
  ⟨by decide, by decide, by decide, by decide⟩
theorem starSym : ArcConsistency.Symmetric starCSP := by unfold ArcConsistency.Symmetric; decide
theorem starTree : IsTreeArcs starCSP starParent := by unfold IsTreeArcs; decide

/-- Without DAC, greedy picks `0` for the centre and gets stuck at leaf `1`. -/
example : greedy starCSP starParent [0, 1, 2, 3] minSel starDom = none := by decide
/-- The original domains are not directionally arc consistent. -/
example : ¬DirArcConsistent starCSP starParent starDom := by
  intro h
  obtain ⟨b, hb, hab⟩ := h 1 0 rfl 0 (Finset.mem_univ _)
  revert b; decide
/-- After the DAC pass the centre's domain is `{2, 3}`. -/
example : (dac starCSP starParent [0, 1, 2, 3] starDom).ret 0 = {2, 3} := by decide
example : treeSolve starCSP starParent [0, 1, 2, 3] minSel starDom = some ![2, 0, 1, 3] := by
  decide
/-- On the DAC domains, greedy succeeds exactly because every domain is nonempty. -/
example : greedy starCSP starParent [0, 1, 2, 3] minSel
    (dac starCSP starParent [0, 1, 2, 3] starDom).ret ≠ none :=
  (greedy_ne_none_iff (isSelector_minSel 4) starOrder starSym starTree
    (dirArcConsistent_dac starOrder _)).2 (by decide)

/-! ## Unsolvable path -/

/-- `x < y` along `0 - 1 - 2` over two values: no solution. -/
def shortCSP : BinaryCSP (Fin 3) (Fin 2) := edgeCSP [(0, 1), (1, 2)] fun a b => a < b

/-- The path rooted at `0`. -/
def shortParent : Fin 3 → Option (Fin 3) := ![none, some 0, some 1]

theorem shortOrder : RootedOrder shortParent [0, 1, 2] :=
  ⟨by decide, by decide, by decide, by decide⟩
theorem shortSym : ArcConsistency.Symmetric shortCSP := by unfold ArcConsistency.Symmetric; decide
theorem shortTree : IsTreeArcs shortCSP shortParent := by unfold IsTreeArcs; decide
theorem shortEdge : ∀ x p, shortParent x = some p → (p, x) ∈ shortCSP.arcs := by decide

example : (dac shortCSP shortParent [0, 1, 2] fun _ => Finset.univ).ret 0 = ∅ := by decide
example : treeSolve shortCSP shortParent [0, 1, 2] minSel (fun _ => Finset.univ) = none := by
  decide

/-- The failed run proves unsolvability. -/
example : ¬∃ σ, IsSolution shortCSP (fun _ => Finset.univ) σ := fun h =>
  (treeSolve_ne_none_iff (isSelector_minSel 2) shortOrder shortSym shortTree shortEdge _).2 h
    (by decide)

/-! ## Cycle counterexample -/

/-- Three pairwise-different variables with two colours. -/
def triangle : BinaryCSP (Fin 3) (Fin 2) := edgeCSP [(0, 1), (1, 2), (0, 2)] fun a b => a ≠ b

/-- The spanning path `0 - 1 - 2`; the arc `(0, 2)` closes the cycle. -/
def triParent : Fin 3 → Option (Fin 3) := ![none, some 0, some 1]

theorem triOrder : RootedOrder triParent [0, 1, 2] :=
  ⟨by decide, by decide, by decide, by decide⟩
example : ArcConsistency.Symmetric triangle := by unfold ArcConsistency.Symmetric; decide

/-- Every arc is consistent, so in particular the domains are directionally arc consistent. -/
example : ∀ e ∈ triangle.arcs, ArcConsistent triangle (fun _ => Finset.univ) e := by
  unfold ArcConsistent; decide
example : DirArcConsistent triangle triParent fun _ => Finset.univ := by
  unfold DirArcConsistent ArcConsistent; decide
/-- Greedy returns an assignment ... -/
example : greedy triangle triParent [0, 1, 2] minSel (fun _ => Finset.univ) = some ![0, 1, 0] := by
  decide
/-- ... that violates the closing arc ... -/
example : ¬IsSolution triangle (fun _ => Finset.univ) ![0, 1, 0] := by unfold IsSolution; decide
/-- ... and no solution exists ... -/
example : ¬∃ σ, IsSolution triangle (fun _ => Finset.univ) σ := by unfold IsSolution; decide
/-- ... because the constraint graph is not the forest of `triParent`. -/
example : ¬IsTreeArcs triangle triParent := by unfold IsTreeArcs; decide

/-! ## Executed fixture: pseudo-random tree CSPs against brute force -/

private meta def check (seed n k : ℕ) (shape : ℕ) : IO Bool := do
  if h : n = 0 then return true else
  have : NeZero n := ⟨h⟩
  let parent : Fin n → Option (Fin n) := fun x =>
    if h0 : x.val = 0 then none
    else if shape = 0 then some ⟨x.val - 1, by have := x.isLt; omega⟩
    else if shape = 1 then some 0
    else some ⟨(seed + 7 * x.val) % x.val,
      Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero h0)) x.isLt⟩
  let edges := (List.finRange n).filterMap fun x => (parent x).map fun p => (p, x)
  let rel : Fin (k + 1) → Fin (k + 1) → Bool := fun a b =>
    (seed + 3 * a.val + 5 * b.val + a.val * b.val) % 5 < 2
  -- the same construction as `edgeCSP` and `minSel`, restated for compile-time evaluation
  let P : BinaryCSP (Fin n) (Fin (k + 1)) := ⟨edges.flatMap fun e => [e, (e.2, e.1)],
    fun x y a b => if (x, y) ∈ edges then rel a b else if (y, x) ∈ edges then rel b a else true⟩
  let sel : Finset (Fin (k + 1)) → Option (Fin (k + 1)) := fun s => s.min
  let dom : Fin n → Finset (Fin (k + 1)) := fun v =>
    Finset.univ.filter fun a => (seed + 2 * v.val + a.val) % 4 != 0
  let order := List.finRange n
  let r := treeSolve P parent order sel dom
  let solvable := decide (∃ σ : Fin n → Fin (k + 1),
    ((List.finRange n).all (fun v => σ v ∈ dom v) &&
      P.arcs.all fun e => P.allowed e.1 e.2 (σ e.1) (σ e.2)) = true)
  let ok := match r with
    | none => !solvable
    | some σ => solvable && (List.finRange n).all (fun v => σ v ∈ dom v) &&
        P.arcs.all fun e => P.allowed e.1 e.2 (σ e.1) (σ e.2)
  let t := (dac P parent order dom).time
  unless ok && t ≤ n * ((k + 1) * (k + 1)) do
    throw (IO.userError s!"seed {seed} n {n} k {k} shape {shape}: mismatch or cost {t}")
  return solvable

#eval do
  let mut solvable := 0
  for i in [0:60] do
    if ← check (i * 7919 + 3) (2 + i % 5) (1 + i % 3) (i % 3) then solvable := solvable + 1
  IO.println s!"60 pseudo-random tree CSPs: treeSolve agrees with brute force ({solvable} solvable)"

#print axioms isSolution_of_greedy_eq_some
#print axioms greedy_ne_none
#print axioms greedy_ne_none_iff
#print axioms dirArcConsistent_dac
#print axioms isSolution_dac
#print axioms dac_time_le
#print axioms dac_time_le_card
#print axioms dirArcConsistent_ac3All
#print axioms isSolution_of_treeSolve_eq_some
#print axioms treeSolve_ne_none_iff

end CSLibExtTest.Algorithms.Lean.CSP.TreeCSP
