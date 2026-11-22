/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Logic.Relation
public import WantedExt.NumberTheory.Digits.PermutipleWanted

/-!
# A multigraph characterization of permutiple strings (Holt)

Statements from Benjamin V. Holt, *A Multigraph Characterization of Permutiple
Strings*, INTEGERS 25 (2025), Article A111 (arXiv:2505.11414).

Permutiples, their digit functions `d : Fin (k + 1) → ℕ` and their carries are those
of `WantedExt/NumberTheory/Digits/PermutipleWanted.lean` (`IsPermutiple`,
`permutipleCarry`), and so is the mother graph `IsMotherGraphEdge` (Definition 4 here,
Definition 4 of Article A13). Inputs of the `(n, b)`-Hoey-Sloane machine are ordered digit pairs
`(d₁, d₂) : ℕ × ℕ`; its states are the carries `0 ≤ c < n`. A cycle of the mother
graph is given by its list of vertices `[v₀, …, v_{r-1}]`, whose edges are
`(v_i, v_{i+1 mod r})`; a multiset of such lists stands for the multiset `I` of cycle
indices of the paper (rotations of a list give the same edge multiset).
-/

namespace MetaMathlibExt

@[expose] public section

/-- Membership in the mother graph is decidable.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 4. -/
public instance (n b d₁ d₂ : ℕ) : Decidable (IsMotherGraphEdge n b d₁ d₂) := by
  unfold IsMotherGraphEdge; infer_instance

/-- Characteristic edges of the `(4, 10)`-mother graph: `(2, 8)` and `(9, 9)` are edges
(`λ(2 + 6 · 8) = 0`, `λ(9 + 6 · 9) = 3`) and `(2, 1)` is not (`λ(2 + 6 · 1) = 8 > 3`).

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 4 and Example 1. -/
public theorem isMotherGraphEdge_four_ten :
    IsMotherGraphEdge 4 10 2 8 ∧ IsMotherGraphEdge 4 10 9 9 ∧ ¬ IsMotherGraphEdge 4 10 2 1 := by
  decide

/-- One transition of the `(n, b)`-Hoey-Sloane machine `Γ`: the input `e = (d₁, d₂)`, an
edge of the mother graph, moves state `c₁` to state `c₂` (both `< n`) when
`b c₂ - c₁ = n d₂ - d₁` (Equation (1)).

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3, Equation (1). -/
public def IsHoeySloaneStep (n b c₁ c₂ : ℕ) (e : ℕ × ℕ) : Prop :=
  c₁ < n ∧ c₂ < n ∧ IsMotherGraphEdge n b e.1 e.2 ∧ (b : ℤ) * c₂ - c₁ = (n : ℤ) * e.2 - e.1

/-- Transitions of the Hoey-Sloane machine are decidable.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3, Equation (1). -/
public instance (n b c₁ c₂ : ℕ) (e : ℕ × ℕ) : Decidable (IsHoeySloaneStep n b c₁ c₂ e) := by
  unfold IsHoeySloaneStep; infer_instance

/-- `IsHoeySloaneRun n b c s c'`: reading the input string `s` from left to right, the
`(n, b)`-Hoey-Sloane machine can go from state `c` to state `c'`.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3. -/
public def IsHoeySloaneRun (n b : ℕ) : ℕ → List (ℕ × ℕ) → ℕ → Prop
  | c, [], c' => c = c'
  | c, e :: s, c' => ∃ c₂, IsHoeySloaneStep n b c c₂ e ∧ IsHoeySloaneRun n b c₂ s c'

/-- The language `L` of the `(n, b)`-Hoey-Sloane machine: input strings defining walks
on `Γ` (`L`-walks) whose initial and final states are zero.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3. -/
public def hoeySloaneLanguage (n b : ℕ) : Set (List (ℕ × ℕ)) :=
  {s | IsHoeySloaneRun n b 0 s 0}

/-- Characteristic example: the inputs `(2, 8)(1, 7)(9, 9)(7, 1)(8, 2)` of
`87912 = 4 · 21978` form a member of the `(4, 10)` language, through the states
`0, 3, 3, 3, 0, 0`.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3 and Example 2. -/
public theorem mem_hoeySloaneLanguage_87912 :
    [(2, 8), (1, 7), (9, 9), (7, 1), (8, 2)] ∈ hoeySloaneLanguage 4 10 := by
  refine ⟨3, by decide, 3, by decide, 3, by decide, 0, by decide, 0, by decide, rfl⟩

/-- An `(n, b)`-permutiple string: a member of `L` which produces a permutiple, i.e. it is
`(d₀, d_{σ(0)})(d₁, d_{σ(1)}) ⋯ (d_k, d_{σ(k)})` for an `(n, b, σ)`-permutiple
`(d_k, …, d₀)_b = n (d_{σ(k)}, …, d_{σ(0)})_b`.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3. -/
public def IsPermutipleString (n b : ℕ) (s : List (ℕ × ℕ)) : Prop :=
  s ∈ hoeySloaneLanguage n b ∧
    ∃ (k : ℕ) (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))),
      IsPermutiple n b d σ ∧ s = List.ofFn fun j => (d j, d (σ j))

/-- Characteristic example: `(2, 8)(1, 7)(9, 9)(7, 1)(8, 2)` is a `(4, 10)`-permutiple
string, produced by `87912 = 4 · 21978`.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3 and Table 1. -/
public theorem isPermutipleString_87912 :
    IsPermutipleString 4 10 [(2, 8), (1, 7), (9, 9), (7, 1), (8, 2)] :=
  ⟨mem_hoeySloaneLanguage_87912, 4, ![2, 1, 9, 7, 8], Fin.revPerm, isPermutiple_87912,
    by decide⟩

/-- The edge list `(v₀, v₁), …, (v_{r-2}, v_{r-1}), (v_{r-1}, v₀)` of the closed walk
with vertex list `[v₀, …, v_{r-1}]`.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 5 (cycles of `M`). -/
public def cycleEdges (vs : List ℕ) : List (ℕ × ℕ) :=
  vs.zip (vs.rotate 1)

/-- Characteristic values: the cycle `2 → 8 → 2` has edges `(2, 8), (8, 2)` and the loop
at `9` has the single edge `(9, 9)`.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Example 2. -/
public theorem cycleEdges_examples :
    cycleEdges [2, 8] = [(2, 8), (8, 2)] ∧ cycleEdges [9] = [(9, 9)] := by
  decide

/-- `vs` lists the vertices of a (directed) cycle of the `(n, b)`-mother graph: it is
nonempty, has no repeated vertex, and each of its edges is an edge of `M` (a loop
`[v]` is a cycle when `(v, v)` is an edge).

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 5 (cycles of `M`). -/
public def IsMotherGraphCycle (n b : ℕ) (vs : List ℕ) : Prop :=
  vs ≠ [] ∧ vs.Nodup ∧ ∀ e ∈ cycleEdges vs, IsMotherGraphEdge n b e.1 e.2

/-- The multiset union `C_I = ⨄_{j ∈ I} C_j` of the edges of the mother-graph cycles in the
multiset `cs`.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 2.3 (multiset cycle union `C_I`). -/
public def cycleUnion (cs : Multiset (List ℕ)) : Multiset (ℕ × ℕ) :=
  cs.bind fun vs => (cycleEdges vs : Multiset (ℕ × ℕ))

/-- The multi-edge `(c₁, c₂)` of the `(n, b)`-Hoey-Sloane multigraph carrying the label
`e = (d₁, d₂)`: `c₁ = λ(d₁ + (b - n) d₂)` and `c₂ = (n d₂ - d₁ + c₁) / b`. For an edge of
`M` this is the unique solution of Equation (1) with `0 ≤ c₁, c₂ ≤ n - 1` (Theorems 5
and 6; see `isHoeySloaneStep_hoeySloaneTransition`).

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 6 and the proof of Theorem 6. -/
public def hoeySloaneTransition (n b : ℕ) (e : ℕ × ℕ) : ℕ × ℕ :=
  let c₁ : ℤ := ((e.1 : ℤ) + ((b : ℤ) - n) * e.2) % b
  (c₁.toNat, (((n : ℤ) * e.2 - e.1 + c₁) / b).toNat)

/-- Characteristic values in the `(4, 10)`-Hoey-Sloane multigraph: the label `(2, 8)` sits
on the multi-edge `0 → 3` and `(1, 7)` on the loop `3 → 3`.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 6 and Figure 4. -/
public theorem hoeySloaneTransition_four_ten :
    hoeySloaneTransition 4 10 (2, 8) = (0, 3) ∧ hoeySloaneTransition 4 10 (1, 7) = (3, 3) := by
  decide

/-- The multigraph union `Δ_I = ⨄_{j ∈ I} Δ_j` of the cycle multi-images, as the multiset of
its multi-edges `(c₁, c₂)` (one per input of `C_I`; the labels are dropped, since they do
not affect in- and out-degrees, connectivity or Eulerian circuits).

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 7. -/
public def multiImageUnion (n b : ℕ) (cs : Multiset (List ℕ)) : Multiset (ℕ × ℕ) :=
  (cycleUnion cs).map (hoeySloaneTransition n b)

/-- The multigraph with multi-edge multiset `D` contains an Eulerian circuit beginning and
ending with the zero state: a nonempty list using every multi-edge exactly once, each
multi-edge ending where the next begins, starting and ending at `0`.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Theorem 7 (hypothesis). -/
public def HasEulerianCircuitFromZero (D : Multiset (ℕ × ℕ)) : Prop :=
  ∃ w : List (ℕ × ℕ), w ≠ [] ∧ (w : Multiset (ℕ × ℕ)) = D ∧
    w.IsChain (fun x y => x.2 = y.1) ∧ w.head?.map Prod.fst = some 0 ∧
    w.getLast?.map Prod.snd = some 0

/-- The multigraph with multi-edge multiset `D` is `L`-Eulerian: it contains the zero state,
it is strongly connected (every vertex reaches every vertex along multi-edges), and the
indegree equals the outdegree at each vertex.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Section 4 (definition of `L`-Eulerian, before
Corollary 2). -/
public def IsLEulerian (D : Multiset (ℕ × ℕ)) : Prop :=
  (∃ x ∈ D, x.1 = 0 ∨ x.2 = 0) ∧
    (∀ u v, (∃ x ∈ D, x.1 = u ∨ x.2 = u) → (∃ x ∈ D, x.1 = v ∨ x.2 = v) →
      Relation.ReflTransGen (fun x y => (x, y) ∈ D) u v) ∧
    ∀ c, D.countP (fun x => x.2 = c) = D.countP (fun x => x.1 = c)

/-- Edge condition: for an `(n, b, σ)`-permutiple, every edge `(d_j, d_{σ(j)})` of its graph
satisfies `λ(d_j + (b - n) d_{σ(j)}) ≤ n - 1`, where `λ` is the least non-negative residue
modulo `b` (computed in `ℤ`). The multiplier is positive (`1 ≤ n`): for `n = 0` the only
permutiples have all digits zero and the bound would read `0 ≤ -1`. This is the case
`π = 1`, `τ = σ` of `permutiple_basePerm_residue_le`.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Theorem 3 (`integers-2025-A111-thm-3`), quoting Holt,
*Finding Permutiples of a Known Base and Multiplier*. -/
public theorem_wanted permutiple_edge_residue_le (n b : ℕ) (hn : 1 ≤ n) {k : ℕ}
    (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ)
    (j : Fin (k + 1)) :
    ((d j : ℤ) + ((b : ℤ) - n) * d (σ j)) % b ≤ (n : ℤ) - 1

/-- The graph of a permutiple class is a union of cycles of the mother graph: for an
`(n, b, σ)`-permutiple `p` (whose class `C` has graph `G_C = G_p`), every edge
`(d_j, d_{σ(j)})` of `G_p` is an edge of `M` and lies on a directed cycle of `G_p`, i.e.
`d_{σ(j)}` reaches `d_j` along edges of `G_p`. The multiplier is positive (`1 ≤ n`).

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Theorem 4 (`integers-2025-A111-thm-4`), quoting Holt,
*Finding Permutiples of a Known Base and Multiplier*. -/
public theorem_wanted permutiple_graph_isUnion_motherGraphCycles (n b : ℕ) (hn : 1 ≤ n) {k : ℕ}
    (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ)
    (j : Fin (k + 1)) :
    IsMotherGraphEdge n b (d j) (d (σ j)) ∧
      Relation.ReflTransGen (fun u v => ∃ i, d i = u ∧ d (σ i) = v) (d (σ j)) (d j)

/-- An input labels at most one transition of `Γ`: if `(d₁, d₂)` induces the transitions
`(c₁, c₂)` and `(ĉ₁, ĉ₂)` of the `(n, b)`-Hoey-Sloane machine, they are equal. The paper's
standing assumption `1 < n < b` is weakened to `n ≤ b`; for `n > b` the claim fails
(`n = 3`, `b = 1`: the input `(0, 0)` induces `(0, 0)` and `(1, 1)`).

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Theorem 5 (`integers-2025-A111-thm-5`). -/
public theorem_wanted isHoeySloaneStep_unique (n b : ℕ) (hnb : n ≤ b) {c₁ c₂ ĉ₁ ĉ₂ : ℕ}
    {e : ℕ × ℕ} (h : IsHoeySloaneStep n b c₁ c₂ e) (ĥ : IsHoeySloaneStep n b ĉ₁ ĉ₂ e) :
    c₁ = ĉ₁ ∧ c₂ = ĉ₂

/-- Every edge `(d₁, d₂)` of the mother graph induces a transition: there are integers
`0 ≤ c₁, c₂ ≤ n - 1` with `b c₂ - c₁ = n d₂ - d₁`.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Theorem 6 (`integers-2025-A111-thm-6`). -/
public theorem_wanted exists_carries_of_isMotherGraphEdge (n b d₁ d₂ : ℕ)
    (h : IsMotherGraphEdge n b d₁ d₂) :
    ∃ c₁ c₂ : ℕ, c₁ ≤ n - 1 ∧ c₂ ≤ n - 1 ∧ (b : ℤ) * c₂ - c₁ = (n : ℤ) * d₂ - d₁

/-- Bridge for Definition 6: for an edge `e` of the mother graph and `1 < n < b`,
`hoeySloaneTransition n b e` is a transition of `Γ` induced by `e` (by
`isHoeySloaneStep_unique`, the only one).

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Definition 6, from Theorems 5 and 6
(`integers-2025-A111-thm-6`). -/
public theorem_wanted isHoeySloaneStep_hoeySloaneTransition (n b : ℕ) (hn : 1 < n) (hnb : n < b)
    (e : ℕ × ℕ) (he : IsMotherGraphEdge n b e.1 e.2) :
    IsHoeySloaneStep n b (hoeySloaneTransition n b e).1 (hoeySloaneTransition n b e).2 e

/-- The inputs of a permutiple string form a union of cycles of the mother graph: every input
`(d, d̂)` of `s` is an edge of `M` and lies on a directed cycle of the graph whose edges are
the inputs of `s` (`d̂` reaches `d`). The paper's standing assumption `1 < n < b` is kept.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Corollary 1 (`integers-2025-A111-cor-1`), quoting Holt,
*Finding Permutiples of a Known Base and Multiplier*. -/
public theorem_wanted isPermutipleString_inputs_isUnion_motherGraphCycles (n b : ℕ) (hn : 1 < n)
    (hnb : n < b) {s : List (ℕ × ℕ)} (hs : IsPermutipleString n b s) (e : ℕ × ℕ)
    (he : e ∈ s) :
    IsMotherGraphEdge n b e.1 e.2 ∧ Relation.ReflTransGen (fun u v => (u, v) ∈ s) e.2 e.1

/-- Sufficient condition (main theorem): let `cs` be a multiset of cycles of the
`(n, b)`-mother graph, with multiset union `C_I` and multi-image union `Δ_I`. If `Δ_I`
contains an Eulerian circuit beginning and ending with the zero state, then `C_I` can be
ordered into a permutiple string.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Theorem 7 (`integers-2025-A111-thm-7`). -/
public theorem_wanted exists_isPermutipleString_of_hasEulerianCircuitFromZero (n b : ℕ) (hn : 1 < n)
    (hnb : n < b) (cs : Multiset (List ℕ)) (hcs : ∀ vs ∈ cs, IsMotherGraphCycle n b vs)
    (h : HasEulerianCircuitFromZero (multiImageUnion n b cs)) :
    ∃ s : List (ℕ × ℕ), (s : Multiset (ℕ × ℕ)) = cycleUnion cs ∧ IsPermutipleString n b s

/-- Characterization: for a multiset `cs` of cycles of the `(n, b)`-mother graph, the
multiset union `C_I` can be ordered into a permutiple string if and only if the multi-image
union `Δ_I` is `L`-Eulerian.

Source: Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*,
INTEGERS 25 (2025), Article A111, Corollary 2 (`integers-2025-A111-cor-2`). -/
public theorem_wanted exists_isPermutipleString_iff_isLEulerian (n b : ℕ) (hn : 1 < n) (hnb : n < b)
    (cs : Multiset (List ℕ)) (hcs : ∀ vs ∈ cs, IsMotherGraphCycle n b vs) :
    (∃ s : List (ℕ × ℕ), (s : Multiset (ℕ × ℕ)) = cycleUnion cs ∧ IsPermutipleString n b s) ↔
      IsLEulerian (multiImageUnion n b cs)

end

end MetaMathlibExt
