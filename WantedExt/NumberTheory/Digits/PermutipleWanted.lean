/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Permutiples with a fixed set of digits (Holt)

Statements from B. V. Holt, *A Method for Finding All Permutiples with a Fixed
Set of Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88
(arXiv:2312.02056).

A `(k+1)`-digit base-`b` numeral `(d_k, …, d_0)_b` is a digit function
`d : Fin (k + 1) → ℕ` (digit `d j` has weight `b ^ j`); for a permutation `π`,
the numeral `(d_{π(k)}, …, d_{π(0)})_b` is `d ∘ π`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- `(d_k, …, d_0)_b` is an `(n, b, σ)`-permutiple: every digit is `< b` and
`(d_k, …, d_0)_b = n · (d_{σ(k)}, …, d_{σ(0)})_b`.

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88,
Definition 1 (from Holt, *Some general results and open questions on
palintiple numbers*). -/
public def IsPermutiple (n b : ℕ) {k : ℕ} (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) :
    Prop :=
  (∀ j, d j < b) ∧ ∑ j, d j * b ^ (j : ℕ) = n * ∑ j, d (σ j) * b ^ (j : ℕ)

/-- The carries `c_j` of the single-digit multiplication `n · (d_{σ(k)}, …, d_{σ(0)})_b`:
`c_0 = 0` and `c_{j+1} = (n d_{σ(j)} + c_j - λ(n d_{σ(j)} + c_j)) / b = ⌊(n d_{σ(j)} + c_j)/b⌋`
for `0 ≤ j ≤ k` (and `0` beyond `k + 1`).

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Section 2. -/
public def permutipleCarry (n b : ℕ) {k : ℕ} (d : Fin (k + 1) → ℕ)
    (σ : Equiv.Perm (Fin (k + 1))) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if h : j < k + 1 then (n * d (σ ⟨j, h⟩) + permutipleCarry n b d σ j) / b else 0

/-- Characteristic values: `c_0 = 0` and `c_1 = ⌊n d_{σ(0)} / b⌋`.

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Section 2. -/
public theorem permutipleCarry_zero_one (n b : ℕ) {k : ℕ} (d : Fin (k + 1) → ℕ)
    (σ : Equiv.Perm (Fin (k + 1))) :
    permutipleCarry n b d σ 0 = 0 ∧ permutipleCarry n b d σ 1 = n * d (σ 0) / b := by
  refine ⟨rfl, ?_⟩
  simp [permutipleCarry]

/-- Characteristic example: `87912 = 4 · 21978` is a `(4, 10, σ)`-permutiple, with
`σ` the digit reversal (`Fin.revPerm`).

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88,
Introduction. -/
public theorem isPermutiple_87912 :
    IsPermutiple 4 10 (k := 4) ![2, 1, 9, 7, 8] Fin.revPerm := by
  unfold IsPermutiple
  decide

/-- Carry relation: for an `(n, b, σ)`-permutiple with carries `c_j`,
`b c_{j+1} - c_j = n d_{σ(j)} - d_j` for all `0 ≤ j ≤ k` (in `ℤ`).

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Theorem 1
(`integers-2024-A88-thm-1`), quoting Holt's earlier paper; restated as Theorem 1
of Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25 (2025),
Article A13 (`integers-2025-A13-thm-1`). -/
public theorem_wanted permutipleCarry_relation (n b : ℕ) (hb : 2 ≤ b) {k : ℕ}
    (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ)
    (j : Fin (k + 1)) :
    (b : ℤ) * permutipleCarry n b d σ (j + 1) - permutipleCarry n b d σ j =
      (n : ℤ) * d (σ j) - d j

/-- Carry bound: for an `(n, b, σ)`-permutiple, every carry satisfies
`c_j ≤ n - 1` (`0 ≤ j ≤ k`).

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Theorem 2
(`integers-2024-A88-thm-2`), quoting Holt's earlier paper; restated as Theorem 2
of Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25 (2025),
Article A13 (`integers-2025-A13-thm-2`). -/
public theorem_wanted permutipleCarry_le (n b : ℕ) (hb : 2 ≤ b) {k : ℕ} (d : Fin (k + 1) → ℕ)
    (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ) (j : Fin (k + 1)) :
    permutipleCarry n b d σ j ≤ n - 1

/-- Necessary condition on the base permutation: if `(d_k, …, d_0)_b` is an
`(n, b, σ)`-permutiple and `(d_{π(k)}, …, d_{π(0)})_b` is an `(n, b, τ)`-permutiple,
then `λ(d_j + (b - n) d_{πτπ⁻¹(j)}) ≤ n - 1` for all `0 ≤ j ≤ k`, where `λ` is
the least non-negative residue modulo `b` (computed in `ℤ`, so `b - n` may be
negative). The multiplier is positive (`1 ≤ n`): for `n = 0` the only permutiple
has all digits zero and the bound would read `0 ≤ -1`.

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Theorem 3
(`integers-2024-A88-thm-3`). -/
public theorem_wanted permutiple_basePerm_residue_le (n b : ℕ) (hn : 1 ≤ n) (hb : 2 ≤ b)
    {k : ℕ} (d : Fin (k + 1) → ℕ) (σ π τ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ)
    (hq : IsPermutiple n b (d ∘ π) τ) (j : Fin (k + 1)) :
    ((d j : ℤ) + ((b : ℤ) - n) * d ((π * τ * π⁻¹) j)) % b ≤ n - 1

/-- The edge set `E_p = {(d_j, d_{σ(j)}) | 0 ≤ j ≤ k}` of the graph `G_p` of a numeral
`(d_k, …, d_0)_b` with digit permutation `σ` (the vertices of `G_p` are all base-`b`
digits, so `G_p` is determined by its edge set).

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Definition 3 (the graph of a permutiple). -/
public def permutipleGraphEdges {k : ℕ} (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) :
    Finset (ℕ × ℕ) :=
  Finset.univ.image fun j => (d j, d (σ j))

/-- Characteristic example: the graph of `87912 = 4 · 21978` has edges
`8 ⇄ 2`, `7 ⇄ 1` and the loop at `9` (Figure 1 of the paper).

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Figure 1. -/
public theorem permutipleGraphEdges_87912 :
    permutipleGraphEdges (k := 4) ![2, 1, 9, 7, 8] Fin.revPerm =
      {(2, 8), (1, 7), (9, 9), (7, 1), (8, 2)} := by
  decide

/-- `(x, y)` is an edge of the `(n, b)`-mother graph `M`: `x` and `y` are base-`b` digits
and `λ(x + (b - n) y) ≤ n - 1`, where `λ` is the least non-negative residue modulo `b`
(computed in `ℤ`).

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Definition 4 (the mother graph). -/
public def IsMotherGraphEdge (n b x y : ℕ) : Prop :=
  x < b ∧ y < b ∧ ((x : ℤ) + ((b : ℤ) - n) * y) % b ≤ (n : ℤ) - 1

/-- Characteristic values: in the `(2, 4)`-mother graph, `(0, 2)` is an edge
(`λ(0 + 2·2) = 0`) and `(0, 1)` is not (`λ(0 + 2·1) = 2 > 1`).

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Definition 4 and Example 1. -/
public theorem isMotherGraphEdge_two_four :
    IsMotherGraphEdge 2 4 0 2 ∧ ¬ IsMotherGraphEdge 2 4 0 1 := by
  unfold IsMotherGraphEdge
  decide

/-- The carries of the `(n, b)`-Hoey-Sloane machine on the input string
`(d_0, d̂_0)(d_1, d̂_1) ⋯ (d_k, d̂_k)`: `c_0 = 0` and `c_{j+1} = (n d̂_j - d_j + c_j) ÷ b`
(integer division in `ℤ`; the transition exists when the division is exact).

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Section 4, Equation (2) (the Hoey-Sloane machine). -/
public def hoeySloaneCarry (n b : ℕ) {k : ℕ} (d dh : Fin (k + 1) → ℕ) : ℕ → ℤ
  | 0 => 0
  | j + 1 =>
    if h : j < k + 1 then
      ((n : ℤ) * dh ⟨j, h⟩ - d ⟨j, h⟩ + hoeySloaneCarry n b d dh j) / b
    else 0

/-- Characteristic example: on the `(2, 4)`-permutiple string `(0,0)(2,3)(1,2)(3,1)` the
Hoey-Sloane machine passes through the states `0, 0, 1, 1, 0` (Figure 4 of the paper).

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Example 1. -/
public theorem hoeySloaneCarry_two_four_example :
    (List.range 5).map (hoeySloaneCarry 2 4 (k := 3) ![0, 2, 1, 3] ![0, 3, 2, 1]) =
      [0, 0, 1, 1, 0] := by
  decide

/-- The input string `(d_0, d̂_0) ⋯ (d_k, d̂_k)` belongs to the language `L` of the
`(n, b)`-Hoey-Sloane machine: every input is an edge of the mother graph, every
transition `c_j → (n d̂_j - d_j + c_j) ÷ b` is an exact division, and the walk starts
and ends in the state `0`.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Section 4 (the language `L` and `L`-walks). -/
public def IsHoeySloaneWord (n b : ℕ) {k : ℕ} (d dh : Fin (k + 1) → ℕ) : Prop :=
  (∀ j, IsMotherGraphEdge n b (d j) (dh j)) ∧
    (∀ j : Fin (k + 1), (b : ℤ) ∣ (n : ℤ) * dh j - d j + hoeySloaneCarry n b d dh j) ∧
      hoeySloaneCarry n b d dh (k + 1) = 0

/-- Edge list of `L`: the `(2, 4)`-permutiple string `(0,0)(2,3)(1,2)(3,1)` lies in `L`.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Example 1. -/
public theorem isHoeySloaneWord_two_four_example :
    IsHoeySloaneWord 2 4 (k := 3) ![0, 2, 1, 3] ![0, 3, 2, 1] := by
  unfold IsHoeySloaneWord IsMotherGraphEdge
  decide

/-- Conjugate permutiples have the same graph: if `(d_{π₁(k)}, …, d_{π₁(0)})_b` is an
`(n, b, τ₁)`-permutiple, `(d_{π₂(k)}, …, d_{π₂(0)})_b` is an `(n, b, τ₂)`-permutiple and
`π₁ τ₁ π₁⁻¹ = π₂ τ₂ π₂⁻¹`, then `G_{p₁} = G_{p₂}`. The permutiple hypotheses (and the
paper's `1 < n < b` and base permutiple `(d_k, …, d_0)_b`) are not needed and are
dropped.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Theorem 4 (`integers-2025-A13-thm-4`). -/
public theorem_wanted permutipleGraphEdges_eq_of_conj {k : ℕ} (d : Fin (k + 1) → ℕ)
    (π₁ π₂ τ₁ τ₂ : Equiv.Perm (Fin (k + 1))) (hconj : π₁ * τ₁ * π₁⁻¹ = π₂ * τ₂ * π₂⁻¹) :
    permutipleGraphEdges (d ∘ π₁) τ₁ = permutipleGraphEdges (d ∘ π₂) τ₂

/-- Every permutiple has a cycle-preserving digit permutation: for every
`(n, b, σ)`-permutiple `(d_k, …, d_0)_b` there is `σ̂` with
`(d_k, …, d_0)_b = n (d_{σ̂(k)}, …, d_{σ̂(0)})_b` such that each cycle
`(j, σ̂(j), …, σ̂^{m-1}(j))` of `σ̂` maps to a graph cycle `(d_j, …, d_{σ̂^{m-1}(j)})` of
`G_p`, i.e. the digits along each `σ̂`-orbit are distinct: `d_{σ̂^i(j)} = d_j` forces
`σ̂^i(j) = j`. The paper's `1 < n < b` is not needed and is dropped.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Theorem 5 (`integers-2025-A13-thm-5`), with Definition 5
(cycle-preserving permutations). -/
public theorem_wanted exists_cyclePreserving_permutiple (n b : ℕ) {k : ℕ}
    (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ) :
    ∃ σ' : Equiv.Perm (Fin (k + 1)), IsPermutiple n b d σ' ∧
      ∀ (j : Fin (k + 1)) (i : ℕ), d ((σ' ^ i) j) = d j → (σ' ^ i) j = j

/-- The graph of a permutiple class is a union of cycles of the mother graph: for an
`(n, b, σ)`-permutiple `p` (so `G_C = G_p` for the class `C` of `p`), every edge of `G_p`
is an edge of `M`, and every edge of `G_p` lies on a directed cycle
`v_0 → v_1 → ⋯ → v_m → v_0` with distinct vertices all of whose edges are in `G_p`.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Theorem 6 (`integers-2025-A13-thm-6`), with Definition 6
(permutiple classes and their graphs). -/
public theorem_wanted permutipleGraphEdges_union_cycles (n b : ℕ) (hn : 1 ≤ n) (hb : 2 ≤ b)
    {k : ℕ} (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ) :
    (∀ e ∈ permutipleGraphEdges d σ, IsMotherGraphEdge n b e.1 e.2) ∧
      ∀ e ∈ permutipleGraphEdges d σ, ∃ (m : ℕ) (v : Fin (m + 1) → ℕ), Function.Injective v ∧
        (∀ i, (v i, v (finRotate (m + 1) i)) ∈ permutipleGraphEdges d σ) ∧
          ∃ i, e = (v i, v (finRotate (m + 1) i))

/-- Permutiple strings are unions of mother-graph cycles: if the input string
`s = (d_0, d̂_0) ⋯ (d_k, d̂_k)` belongs to the Hoey-Sloane language `L` and is a
permutiple string (`d̂_j = d_{σ(j)}` for a permutation `σ`), then its set of inputs is a
union of cycles of `M` (every input lies on a directed cycle with distinct vertices
built from inputs of `s`). The record's trailing remarks (converse fails) are omitted.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Corollary 1 (`integers-2025-A13-cor-1`). -/
public theorem_wanted hoeySloaneWord_inputs_union_cycles (n b : ℕ) (hn : 1 ≤ n) (hb : 2 ≤ b)
    {k : ℕ} (d dh : Fin (k + 1) → ℕ) (hs : IsHoeySloaneWord n b d dh)
    (σ : Equiv.Perm (Fin (k + 1))) (hσ : dh = d ∘ σ) :
    ∀ e ∈ Finset.univ.image (fun j => (d j, dh j)), ∃ (m : ℕ) (v : Fin (m + 1) → ℕ),
      Function.Injective v ∧
        (∀ i, (v i, v (finRotate (m + 1) i)) ∈ Finset.univ.image (fun j => (d j, dh j))) ∧
          ∃ i, e = (v i, v (finRotate (m + 1) i))

end

end MetaMathlibExt
