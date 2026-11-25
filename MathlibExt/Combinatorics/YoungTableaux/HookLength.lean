/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SymmetricFunctionsYoungTableaux
public import Mathlib.Combinatorics.Young.YoungDiagram
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Hook lengths and the number of standard Young tableaux

For a Young diagram `λ` (Mathlib's `YoungDiagram`, cells `(i, j)` indexed from `0`):

* `hookLength λ c`: the hook length `h(u)` of a cell, the number of cells to its right in its row,
  below it in its column, and itself;
* `sytCount λ`: the number `f^λ` of standard Young tableaux of shape `λ`, counted with the
  repository's `MetaMathlibExt.SkewStandardYoungTableau` of skew shape `λ/∅`;
* `finite_standardYoungTableau`: there are finitely many such tableaux, so `f^λ` is their actual
  number.

The hook length formula is recorded in `WantedExt.Combinatorics.YoungTableaux.HookLengthWanted`.
The sum of squares identity is proved in `MathlibExt.Combinatorics.YoungTableaux.SumSYTCountSq`.
Source: Stanley, *Topics in Algebraic Combinatorics*, author's draft of
1 February 2013 (https://math.mit.edu/~rstan/algcomb/algcomb.pdf), Chapter 8; published as
*Algebraic Combinatorics: Walks, Trees, Tableaux, and More* (Springer, 2013).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.YoungTableaux.HookLength

open MetaMathlibExt

/-- **Straight shape as a skew shape.** The skew shape `λ/∅`, whose standard Young tableaux are
the standard Young tableaux of shape `λ`. -/
def straightShape (μ : YoungDiagram) : SkewShape := ⟨μ, ⊥, bot_le⟩

/-- **Hook length of a cell.** For a cell `u = (i, j)` of the Young diagram `λ` (rows and columns
indexed from `0`), the hook length `h(u)` is the number of cells directly to the right of `u` in
its row, directly below `u` in its column, plus `1` for `u` itself:
`h(i, j) = (λᵢ - j) + (λ'ⱼ - i) - 1`, with `λᵢ` the length of row `i` and `λ'ⱼ` that of column
`j` (Stanley, *Topics in Algebraic Combinatorics*, author's draft of 1 February 2013,
Chapter 8, before Theorem 8.1). For `λ = (4, 2, 2)` the hook lengths of the first row are
`6, 5, 2, 1`. -/
def hookLength (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  μ.rowLen c.1 - c.2 + (μ.colLen c.2 - c.1) - 1

/-- **Hook lengths are positive.** Every cell of a Young diagram has hook length at least `1`. -/
theorem hookLength_pos {μ : YoungDiagram} {c : ℕ × ℕ} (hc : c ∈ μ) : 0 < hookLength μ c := by
  have h1 : c.2 < μ.rowLen c.1 := YoungDiagram.mem_iff_lt_rowLen.mp hc
  have h2 : c.1 < μ.colLen c.2 := YoungDiagram.mem_iff_lt_colLen.mp hc
  unfold hookLength
  omega

/-- **Number of standard Young tableaux.** `f^λ` is the number of standard Young tableaux of
shape `λ`, that is, of fillings of the cells of `λ` with `1, 2, …, n` (`n = |λ|`), each used once,
increasing along rows and down columns (Stanley, *Topics in Algebraic Combinatorics*, author's
draft of 1 February 2013, Chapter 8). -/
noncomputable def sytCount (μ : YoungDiagram) : ℕ :=
  Nat.card (SkewStandardYoungTableau (straightShape μ))

/-- **Tableaux are determined by their entries.** Two standard Young tableaux of the same skew
shape with the same entries are equal. -/
theorem SkewStandardYoungTableau.ext' {s : SkewShape} {T T' : SkewStandardYoungTableau s}
    (h : T.entry = T'.entry) : T = T' := by
  obtain ⟨⟨e, _, _, _, _⟩, _⟩ := T
  obtain ⟨⟨e', _, _, _, _⟩, _⟩ := T'
  cases h
  rfl

/-- **Finitely many standard Young tableaux.** For every skew shape there are finitely many
standard Young tableaux: the entries vanish off the cells and lie in `{1, …, n}` on them. Hence
`sytCount λ` is the number of standard Young tableaux of shape `λ`, not a `Nat.card` default. -/
instance finite_standardYoungTableau (s : SkewShape) : Finite (SkewStandardYoungTableau s) := by
  classical
  set C := s.outer.cells \ s.inner.cells
  let F : SkewStandardYoungTableau s → (C → Fin (C.card + 1)) := fun T c =>
    ⟨T.entry c.1.1 c.1.2, Nat.lt_succ_of_le (T.bijOn.mapsTo (Finset.mem_coe.mpr c.2)).2⟩
  refine Finite.of_injective F fun T T' hTT' => SkewStandardYoungTableau.ext' ?_
  funext i j
  by_cases hc : (i, j) ∈ C
  · have := congrFun hTT' ⟨(i, j), hc⟩
    simpa [F] using congrArg Fin.val this
  · have hnot : ¬ ((i, j) ∈ s.outer ∧ (i, j) ∉ s.inner) := by
      simpa [C, Finset.mem_sdiff, YoungDiagram.mem_cells] using hc
    rw [T.zeros hnot, T'.zeros hnot]

end MathlibExt.Combinatorics.YoungTableaux.HookLength
