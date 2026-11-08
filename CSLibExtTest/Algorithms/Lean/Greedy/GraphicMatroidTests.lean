/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Greedy.GraphicMatroid
public meta import CSLibExt.Algorithms.Lean.Greedy.GraphicMatroid

/-!
# The graphic matroid and Kruskal's algorithm: tests

Executed fixtures on complete graphs with symmetric weights: each run sorts the edges by
nonincreasing weight, runs `matroidGreedy` with `forestOracle`, and compares the result with a
brute force over all edge subsets that tests acyclicity with its own reachability closure (an edge
set is a forest iff deleting any of its edges disconnects that edge's endpoints). It throws if the
result is not a forest or not of maximum weight. Closed checks: the theorems applied to `⊤`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.GraphicMatroid

open Cslib.Algorithms.Lean.TimeM

/-- An edge as the pair `(min, max)` of its endpoints. -/
private def toPair {n : ℕ} : Sym2 (Fin n) → ℕ × ℕ :=
  Sym2.lift ⟨fun a b => (min a.val b.val, max a.val b.val), fun a b => by
    simp [min_comm, max_comm]⟩

/-- A symmetric weight. -/
private def wtP (p : ℕ × ℕ) : ℕ := (p.1 * p.2 * 7 + p.1 + p.2 + 3) % 11

private def wt {n : ℕ} (e : Sym2 (Fin n)) : ℕ := wtP (toPair e)

/-- The edges `s(u, v)` with `u < v`. -/
private def edges (n : ℕ) : List (Sym2 (Fin n)) :=
  (List.finRange n).flatMap fun u => ((List.finRange n).filter (u < ·)).map fun v => s(u, v)

/-- Reachability inside a list of edges (as pairs), by closure. -/
private def reach (n : ℕ) (es : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  let step (s : List ℕ) : List ℕ := (List.range n).filter fun x => x ∈ s ||
    es.any fun e => (e.1 ∈ s && e.2 == x) || (e.2 ∈ s && e.1 == x)
  v ∈ (List.range n).foldl (fun s _ => step s) [u]

/-- Brute-force forest test. -/
private def isForest (n : ℕ) (es : List (ℕ × ℕ)) : Bool :=
  es.all fun e => !reach n (es.erase e) e.1 e.2

/-- Brute force: the heaviest forest among all subsets of the edges. -/
private def bruteMax (n : ℕ) (es : List (ℕ × ℕ)) : ℕ :=
  (es.sublists.filter (isForest n)).foldl (fun best s => max best (s.map wtP).sum) 0

private def check (label : String) (n : ℕ) : IO Unit := do
  let es := (edges n).mergeSort fun a b => decide (wt b ≤ wt a)
  let T := (matroidGreedy (forestOracle (⊤ : SimpleGraph (Fin n))) es).ret
  let got := ((edges n).filter (· ∈ T)).map toPair
  let w := (got.map wtP).sum
  let best := bruteMax n ((edges n).map toPair)
  unless isForest n got && w == best && got.length + 1 == n do
    throw (IO.userError s!"{label}: result {got} weighs {w}, brute-force maximum {best}")
  IO.println s!"{label}: spanning tree {got}, weight {w} = maximum {best}"

#eval check "K3" 3
#eval check "K4" 4
#eval check "K5" 5

example : IsForestSet (⊤ : SimpleGraph (Fin 4))
    ↑(matroidGreedy (forestOracle (⊤ : SimpleGraph (Fin 4))) (edges 4)).ret :=
  kruskal_isForest _

example {I : Finset (Sym2 (Fin 4))} (hI : IsForestSet (⊤ : SimpleGraph (Fin 4)) ↑I)
    (hsorted : (edges 4).Pairwise fun a b => wt b ≤ wt a) (hIes : ∀ x ∈ I, x ∈ edges 4) :
    ∑ x ∈ I, wt x ≤
      ∑ x ∈ (matroidGreedy (forestOracle (⊤ : SimpleGraph (Fin 4))) (edges 4)).ret, wt x :=
  kruskal_optimal wt hsorted hI hIes

#print axioms exists_insert_isAcyclic
#print axioms ncard_edgeSet_add_card_connectedComponent
#print axioms forestOracle_iff
#print axioms kruskal_optimal
#print axioms kruskal_isBase

end Cslib.Algorithms.Lean.GraphicMatroid
