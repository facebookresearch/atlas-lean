/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

/- Primary source: Wentao T. Lu and F. Y. Wu, "Close-packed dimers on
nonorientable surfaces", arXiv:cond-mat/0110035v3
(<https://arxiv.org/abs/cond-mat/0110035>).
Grid/generating-function display (gen), lines 145-163;
odd-column Mobius-grid formula (Mob-2), lines 184-188;
M-even Mobius-strip setup with grid dimensions (2M, N) and the twisted
adjacency matrix, lines 264-311.
Only the unweighted odd-column Mobius-grid formula is formalized here;
the Klein-bottle and even-N variants are not encoded. -/

/-- **Vertices of the Möbius grid.** For natural numbers $M$ and $N$, the vertices of the
$2M \times N$ Möbius grid are the pairs $(a, b)$ of natural numbers with $a < 2M$ and $b < N$. -/
def MobiusGridVertex (M N : ℕ) : Type :=
  Fin (2 * M) × Fin N

/-- **Edges of the Möbius grid.** For natural numbers $M$ and $N$, the labeled edges of the
$2M \times N$ Möbius grid are of three kinds: a horizontal edge $h(i, j)$ for each row $i < 2M$
and column $j < N - 1$, a vertical edge $v(i, j)$ for each row $i < 2M - 1$ and column $j < N$,
and a seam edge $\sigma(i)$ for each row $i < 2M$.

Edges with different labels are different, even when small dimensions make two of them join the
same pair of vertices; this keeps the edge-labeled dimer multiplicities of the source. -/
inductive MobiusGridEdge (M N : ℕ) where
  | horizontal (row : Fin (2 * M)) (col : Fin (N - 1)) : MobiusGridEdge M N
  | vertical (row : Fin (2 * M - 1)) (col : Fin N) : MobiusGridEdge M N
  | seam (row : Fin (2 * M)) : MobiusGridEdge M N
deriving DecidableEq, Fintype

/-- **Incidence in the Möbius grid.** For natural numbers $M$ and $N$, write a vertex of the
$2M \times N$ Möbius grid as $(a, b)$ with row $a < 2M$ and column $b < N$. The vertex $(a, b)$
is incident to the horizontal edge $h(i, j)$ (with $i < 2M$, $j < N - 1$) exactly when $a = i$
and $b \in \{j, j + 1\}$; to the vertical edge $v(i, j)$ (with $i < 2M - 1$, $j < N$) exactly
when $b = j$ and $a \in \{i, i + 1\}$; and to the seam edge $\sigma(i)$ (with $i < 2M$) exactly
when $(a, b) = (i, N - 1)$ or $(a, b) = (2M - 1 - i, 0)$. -/
def MobiusGridIncident {M N : ℕ} (e : MobiusGridEdge M N)
    (v : MobiusGridVertex M N) : Prop :=
  match e with
  | .horizontal row col =>
      v.1.val = row.val ∧ (v.2.val = col.val ∨ v.2.val = col.val + 1)
  | .vertical row col =>
      v.2.val = col.val ∧ (v.1.val = row.val ∨ v.1.val = row.val + 1)
  | .seam row =>
      (v.1.val = row.val ∧ v.2.val = N - 1) ∨
        (v.1.val = 2 * M - 1 - row.val ∧ v.2.val = 0)

/-- **Perfect matchings of the Möbius grid.** For natural numbers $M$ and $N$, a finite set $S$
of labeled edges of the $2M \times N$ Möbius grid is a perfect matching when every vertex of the
grid is incident to exactly one edge of $S$. -/
def IsMobiusGridPerfectMatching {M N : ℕ}
    (S : Finset (MobiusGridEdge M N)) : Prop :=
  ∀ v : MobiusGridVertex M N, ∃! e, e ∈ S ∧ MobiusGridIncident e v

/-- **Number of perfect matchings of the Möbius grid.** For natural numbers $M$ and $N$, this is
the number of perfect matchings of the $2M \times N$ Möbius grid, counted as sets of labeled
edges. -/
noncomputable def mobiusGridPerfectMatchingCount (M N : ℕ) : ℕ :=
  by
    classical
    exact Fintype.card
      {S : Finset (MobiusGridEdge M N) //
        IsMobiusGridPerfectMatching (M := M) (N := N) S}

/-- **Lu–Wu formula for perfect matchings of the Möbius grid.** Let $M \ge 1$ and let $N \ge 1$
be odd. Then the number of perfect matchings of the $2M \times N$ Möbius grid equals

$$
\operatorname{Re}\Big[(1 - i) \prod_{s=1}^{M} \prod_{r=1}^{N}
\Big(2i\,(-1)^{M+s+1} \sin\frac{(4r-1)\pi}{2N} + 2\cos\frac{s\pi}{2M+1}\Big)\Big].
$$

This is the unweighted formula for an odd number of columns. -/
theorem_wanted lu_wu_mobius_grid_perfect_matching_count {M N : ℕ}
    (hM : 0 < M) (hN : 0 < N) (hNodd : Odd N) :
    (mobiusGridPerfectMatchingCount M N : ℝ) =
      Complex.re
        ((1 - Complex.I) *
          ∏ s ∈ Finset.Icc 1 M, ∏ r ∈ Finset.Icc 1 N,
            (2 * Complex.I * (-1 : ℂ) ^ (M + s + 1) *
                ↑(Real.sin ((((4 * r - 1 : ℕ) : ℝ)) * Real.pi / (2 * (N : ℝ)))) +
              2 * ↑(Real.cos ((s : ℝ) * Real.pi / (2 * (M : ℝ) + 1)))))

end MetaMathlibExt
