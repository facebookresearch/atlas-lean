/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Convex.Hull

/-!
# Positivity on a shadow Markoff tree

Statements from Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of
Integer Sequences 27 (2024), Article 24.8.3 (arXiv:2403.07668; TeX source read for the
definitions).

A solution `(A, B, C) = (a + αε, b + βε, c + γε)` of the shadow Markoff equation
`A² + B² + C² = (3 - σε) ABC` (`ε² = 0`) is stored as the pair `(x, y)` of its classical part
`x = (a, b, c)` and its shadow part `y = (α, β, γ)`. The mutation at position `i` replaces
`x_i` by `x_i' = (x_j² + x_k²) / x_i` and `y_i` by `(-x_i' y_i + 2 x_j y_j + 2 x_k y_k) / x_i`
(`{i, j, k} = {0, 1, 2}`). The tree of an initial triple `(1 + αε, 1 + βε, 1 + γε)` is the
classical Markoff tree as drawn in the paper: the root, then the mutation at position `0`, then
at position `1` (the paper's `(1,1,1)`, `(1,1,2)`, `(1,2,5)`), then every non-backtracking
sequence of mutations.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The shadow Markoff mutation at position `i` of a state `(x, y)` (classical part `x`, shadow
part `y`): `x_i ↦ x_i' = (∑_{j ≠ i} x_j²) / x_i` and `y_i ↦ (-x_i' y_i + 2 ∑_{j ≠ i} x_j y_j) / x_i`.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Section 1, equations (MutA) and (SMarmutBis). -/
def shadowMarkoffMutate (i : Fin 3) (s : (Fin 3 → ℚ) × (Fin 3 → ℚ)) :
    (Fin 3 → ℚ) × (Fin 3 → ℚ) :=
  let x' : ℚ := (∑ j ∈ Finset.univ.erase i, s.1 j ^ 2) / s.1 i
  (Function.update s.1 i x',
    Function.update s.2 i ((-x' * s.2 i + 2 * ∑ j ∈ Finset.univ.erase i, s.1 j * s.2 j) / s.1 i))

/-- The initial triple `(1 + αε, 1 + βε, 1 + γε)` of shadow part `v = (α, β, γ) ∈ ℤ³`.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Section 1, equation (InitTrip). -/
def shadowMarkoffRoot (v : Fin 3 → ℤ) : (Fin 3 → ℚ) × (Fin 3 → ℚ) :=
  (fun _ => 1, fun i => (v i : ℚ))

/-- The nodes below `(1,1,2)` of the shadow Markoff tree of the initial triple with shadow part
`v`, tagged with the position mutated last: the node `(1,2,5)` (mutations at `0`, then `1`), and
every mutation at a position other than the last one.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Section 2 (the classical Markoff tree: "The initial triple
`(1,1,1)` is the root of the tree. It is followed by `(1,1,2)` and `(1,2,5)`. After that, any
mutation is allowed.") and Section 4. -/
inductive ShadowMarkoffTreeNode (v : Fin 3 → ℤ) : (Fin 3 → ℚ) × (Fin 3 → ℚ) → Fin 3 → Prop
  | start :
      ShadowMarkoffTreeNode v (shadowMarkoffMutate 1 (shadowMarkoffMutate 0 (shadowMarkoffRoot v))) 1
  | mutate {s : (Fin 3 → ℚ) × (Fin 3 → ℚ)} {l : Fin 3} (i : Fin 3) :
      ShadowMarkoffTreeNode v s l → i ≠ l → ShadowMarkoffTreeNode v (shadowMarkoffMutate i s) i

/-- The solutions of the shadow Markoff tree of the initial triple with shadow part `v`: the root,
its mutation at position `0`, and the nodes of `ShadowMarkoffTreeNode v`.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Sections 2 and 4. -/
def shadowMarkoffTree (v : Fin 3 → ℤ) : Set ((Fin 3 → ℚ) × (Fin 3 → ℚ)) :=
  {shadowMarkoffRoot v, shadowMarkoffMutate 0 (shadowMarkoffRoot v)} ∪
    {s | ∃ l, ShadowMarkoffTreeNode v s l}

/-- The first two mutations of the tree of `(1, 1, 1 + ε)` (the paper's vertex `(0:0:1)`):
`(1,1,1 | 0,0,1) ↦ (2,1,1 | 2,0,1) ↦ (2,5,1 | 2,10,1)`, matching the labels `2 2` and `5 10` of
the paper's figure.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Section 4.1 (the tree of the vertex `(0:0:1)`). -/
theorem shadowMarkoffMutate_vertex_001 :
    shadowMarkoffMutate 0 (shadowMarkoffRoot ![0, 0, 1]) = (![2, 1, 1], ![2, 0, 1]) ∧
      shadowMarkoffMutate 1 (shadowMarkoffMutate 0 (shadowMarkoffRoot ![0, 0, 1])) =
        (![2, 5, 1], ![2, 10, 1]) := by
  have h0 : shadowMarkoffMutate 0 (shadowMarkoffRoot ![0, 0, 1]) = (![2, 1, 1], ![2, 0, 1]) := by
    ext i <;> fin_cases i <;>
      simp [shadowMarkoffMutate, shadowMarkoffRoot, Function.update, Finset.sum_erase_eq_sub,
        Fin.sum_univ_three]
  refine ⟨h0, ?_⟩
  rw [h0]
  ext i <;> fin_cases i <;>
    simp [shadowMarkoffMutate, Function.update, Finset.sum_erase_eq_sub, Fin.sum_univ_three] <;>
    norm_num

/-- There is a finite set `V ⊆ ℚ³` (a convex polygon `conv V` in an affine chart of `ℚP²`) such
that for every initial triple `(1 + αε, 1 + βε, 1 + γε)` with `v = (α, β, γ) ∈ ℤ³`, every solution
of its shadow Markoff tree is nonnegative if and only if `v` lies in the cone over `conv V`, i.e.
the point `(α : β : γ)` belongs to the polygon.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Theorem 2 (`jis-2024-24.8.3-thm-2`). -/
public theorem_wanted exists_polygon_shadowMarkoffTree_nonneg_iff :
    ∃ V : Finset (Fin 3 → ℚ), ∀ v : Fin 3 → ℤ,
      (∀ s ∈ shadowMarkoffTree v, 0 ≤ s.1 ∧ 0 ≤ s.2) ↔
        ∃ t : ℚ, 0 ≤ t ∧ ∃ p ∈ convexHull ℚ (V : Set (Fin 3 → ℚ)), (fun i => (v i : ℚ)) = t • p

/-- In the shadow Markoff tree of the initial triple `(1 + ε, 1 + ε, 1 + ε)` the shadow part of
every solution equals its classical part: the shadow tree coincides with the classical Markoff
tree.

Source: Nathan Bonin, *Conditions of Positivity on a Shadow Markoff Tree*, Journal of Integer
Sequences 27 (2024), Article 24.8.3, Lemma 3 (`jis-2024-24.8.3-lem-3`). -/
public theorem_wanted shadowMarkoffTree_one_shadow_eq :
    ∀ s ∈ shadowMarkoffTree (fun _ => 1), s.2 = s.1

end

end MetaMathlibExt
