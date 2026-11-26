/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.ENat.Lattice

/-!
# Count-to-infinity in distance-vector routing

The nodes of a network are the vertices of a simple graph `G`, whose edges are the links, and
`c x v : ℕ` is the cost of the direct link from `x` to `v`. In distance-vector routing each node
`x` keeps an estimate `D x y : ℕ∞` of its distance to every destination `y`, where `⊤` means
that `x` knows no route to `y`. In a round, every node recomputes its estimates from those its
neighbors held before the round: its estimate of its distance to itself is `0`, and for every
other destination `y` its new estimate is the minimum, over its neighbors `v`, of
`c x v + D v y`. The neighbors' estimates are the only information used; no paths are
exchanged.

## Main definitions

* `step G c D`: the estimates after one round of distance-vector updates on the network `G`
  with link costs `c`, from the estimates `D`.

## Main results

* `count_to_infinity`: on the path `A - B - C` with `c(A, B) = c(B, A) = 1` and `c(B, C) = 2`,
  the estimates `D_A(C) = 3`, `D_B(C) = 2` and `D_C(C) = 0` are unchanged by a round. After the
  link `B - C` fails, `k` rounds give `D_A(C) = 3 + 2 ⌊k / 2⌋` and `D_B(C) = 2 + 2 ⌈k / 2⌉`: in
  each round one of the two estimates increases by `2`, alternately that of `B` and that of
  `A`, and both remain finite and exceed every bound.

## References

* A. C. Snoeren, *Distance-vector Routing*, Lecture 13 of CSE 123: Computer Networks, UC San
  Diego, Fall 2010: the update rule on slide 5 and the example "Counting to Infinity" on
  slide 13.
-/

@[expose] public section

namespace Cslib.Algorithms.Networking.DistanceVector

open SimpleGraph

variable {V : Type*}

/-- **Distance-vector round.** Let $G$ be a simple graph whose vertices are the nodes of a
network and whose edges are its links, let $c(x, v) \in \mathbb{N}$ be the cost of the direct link
from $x$ to $v$, and let $D_x(y) \in \mathbb{N} \cup \{\infty\}$ be the estimate of node $x$ of its
distance to node $y$, where $\infty$ means that $x$ knows no route to $y$. In one round every node
recomputes its estimates from those its neighbors held before the round: node $x$ estimates
its distance to itself as $0$ and its distance to every other node $y$ as

$$D'_x(y) = \min_{v \sim x} \bigl(c(x, v) + D_v(y)\bigr),$$

the minimum over the neighbors $v$ of $x$ in $G$, which is $\infty$ when $x$ has no neighbor.

Source: A. C. Snoeren, *Distance-vector Routing*, Lecture 13 of CSE 123: Computer Networks,
UC San Diego, Fall 2010, slide 5. -/
noncomputable def step [DecidableEq V] (G : SimpleGraph V) (c : V → V → ℕ) (D : V → V → ℕ∞)
    (x y : V) : ℕ∞ :=
  if x = y then 0 else ⨅ (v : V) (_ : G.Adj x v), (c x v : ℕ∞) + D v y

/-- A minimum over the neighbors of a vertex whose only neighbor is `v` is the value at `v`. -/
private theorem iInf_adj_of_unique {G : SimpleGraph V} {x v : V}
    (hv : ∀ w, G.Adj x w ↔ w = v) (f : V → ℕ∞) :
    ⨅ (w : V) (_ : G.Adj x w), f w = f v :=
  le_antisymm (iInf₂_le v ((hv v).2 rfl))
    (le_iInf₂ fun w hw ↦ ((hv w).1 hw).symm ▸ le_rfl)

/-- **Count-to-infinity in distance-vector routing.** Let $A, B, C$ be the vertices $0, 1, 2$
of the path graph $A - B - C$, with link costs $c(A, B) = c(B, A) = 1$ and $c(B, C) = 2$, and
let $D$ be estimates with $D_A(C) = 3$, $D_B(C) = 2$ and $D_C(C) = 0$, the others arbitrary;
$A$ routes to $C$ through $B$, its only neighbor. Then:

* before any failure, a round of distance-vector updates (`step`) leaves every estimate of the
  distance to $C$ unchanged;
* after the link $B - C$ fails, $k$ rounds on the remaining network give
  $D_A(C) = 3 + 2 \lfloor k/2 \rfloor$ and $D_B(C) = 2 + 2 \lceil k/2 \rceil$, so that in each
  round one of the two estimates increases by $2$, alternately that of $B$ and that of $A$,
  and both remain finite;
* these estimates increase without bound: for every $n \in \mathbb{N}$ there is a $k$ such that
  after $k$ rounds both exceed $n$.

Source: A. C. Snoeren, *Distance-vector Routing*, Lecture 13 of CSE 123: Computer Networks,
UC San Diego, Fall 2010, slide 13. -/
theorem count_to_infinity {c : Fin 3 → Fin 3 → ℕ} (hAB : c 0 1 = 1) (hBA : c 1 0 = 1)
    (hBC : c 1 2 = 2) {D : Fin 3 → Fin 3 → ℕ∞} (hA : D 0 2 = 3) (hB : D 1 2 = 2)
    (hC : D 2 2 = 0) :
    (∀ x, step (pathGraph 3) c D x 2 = D x 2) ∧
      (∀ k, (step ((pathGraph 3).deleteEdges {s(1, 2)}) c)^[k] D 0 2 =
          ((3 + 2 * (k / 2) : ℕ) : ℕ∞) ∧
        (step ((pathGraph 3).deleteEdges {s(1, 2)}) c)^[k] D 1 2 =
          ((2 + 2 * ((k + 1) / 2) : ℕ) : ℕ∞)) ∧
      ∀ n : ℕ, ∃ k, (n : ℕ∞) < (step ((pathGraph 3).deleteEdges {s(1, 2)}) c)^[k] D 0 2 ∧
        (n : ℕ∞) < (step ((pathGraph 3).deleteEdges {s(1, 2)}) c)^[k] D 1 2 := by
  set G := (pathGraph 3).deleteEdges {s(1, 2)}
  have hGA : ∀ w, G.Adj 0 w ↔ w = 1 := by
    intro w; fin_cases w <;> simp [G, pathGraph_adj]
  have hGB : ∀ w, G.Adj 1 w ↔ w = 0 := by
    intro w; fin_cases w <;> simp [G, pathGraph_adj]
  have hstepA : ∀ E, step G c E 0 2 = 1 + E 1 2 := by
    intro E
    rw [step, ite_eq_right (by decide), iInf_adj_of_unique hGA, hAB, Nat.cast_one]
  have hstepB : ∀ E, step G c E 1 2 = 1 + E 0 2 := by
    intro E
    rw [step, ite_eq_right (by decide), iInf_adj_of_unique hGB, hBA, Nat.cast_one]
  have hiter : ∀ k, (step G c)^[k] D 0 2 = ((3 + 2 * (k / 2) : ℕ) : ℕ∞) ∧
      (step G c)^[k] D 1 2 = ((2 + 2 * ((k + 1) / 2) : ℕ) : ℕ∞) := by
    intro k
    induction k with
    | zero => simp [hA, hB]
    | succ k ih =>
      rw [Function.iterate_succ_apply', hstepA, hstepB, ih.1, ih.2]
      have h₁ : 1 + (2 + 2 * ((k + 1) / 2)) = 3 + 2 * ((k + 1) / 2) := by omega
      have h₂ : 1 + (3 + 2 * (k / 2)) = 2 + 2 * ((k + 1 + 1) / 2) := by omega
      exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
  refine ⟨fun x ↦ ?_, hiter, fun n ↦ ⟨2 * n, ?_⟩⟩
  · have hPA : ∀ w, (pathGraph 3).Adj 0 w ↔ w = 1 := by
      intro w; fin_cases w <;> simp [pathGraph_adj]
    have hPB : ∀ w, (pathGraph 3).Adj 1 w ↔ w = 0 ∨ w = 2 := by
      intro w; fin_cases w <;> simp [pathGraph_adj]
    fin_cases x
    · change step (pathGraph 3) c D 0 2 = D 0 2
      rw [step, ite_eq_right (by decide), iInf_adj_of_unique hPA, hAB, hB, hA]
      rfl
    · change step (pathGraph 3) c D 1 2 = D 1 2
      rw [step, ite_eq_right (by decide), hB]
      refine le_antisymm ((iInf₂_le 2 ((hPB 2).2 (Or.inr rfl))).trans ?_)
        (le_iInf₂ fun w hw ↦ ?_)
      · rw [hBC, hC]
        rfl
      · rcases (hPB w).1 hw with rfl | rfl
        · rw [hBA, hA]
          decide
        · rw [hBC, hC]
          rfl
    · change step (pathGraph 3) c D 2 2 = D 2 2
      rw [step, ite_eq_left rfl, hC]
  · rw [(hiter (2 * n)).1, (hiter (2 * n)).2]
    constructor <;> exact Nat.cast_lt.2 (by omega)

end Cslib.Algorithms.Networking.DistanceVector
