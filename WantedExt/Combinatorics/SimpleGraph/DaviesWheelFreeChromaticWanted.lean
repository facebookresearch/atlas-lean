/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Triangle-free wheel-free graphs with large chromatic number
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.DaviesWheelFreeChromaticWanted

/-- **Induced wheels.** A simple graph $G$ has an induced wheel if there are a natural
number $\ell \ge 4$, distinct vertices $r_0, \dots, r_{\ell-1}$ of $G$ (the rim) and a vertex
$h$ of $G$ (the hub) with $h \ne r_i$ for every $i$, such that for all $i, j < \ell$ the
vertices $r_i$ and $r_j$ are adjacent in $G$ exactly when $i - j \equiv \pm 1 \pmod{\ell}$,
and $h$ is adjacent to $r_i$, $r_j$ and $r_k$ for some pairwise distinct $i, j, k < \ell$.
The hub may have further neighbours on the rim.

Source: James Davies, *Triangle-free graphs with large chromatic number and no
induced wheel*, arXiv:2104.05907v3, page 1, defining paragraph,
https://arxiv.org/pdf/2104.05907v3. -/
def hasInducedWheel {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (ℓ : ℕ) (rim : Fin ℓ ↪ V) (hub : V),
    4 ≤ ℓ ∧
    (∀ i : Fin ℓ, rim i ≠ hub) ∧
    (∀ i j : Fin ℓ, G.Adj (rim i) (rim j) ↔ (SimpleGraph.cycleGraph ℓ).Adj i j) ∧
    ∃ i j k : Fin ℓ, i ≠ j ∧ j ≠ k ∧ k ≠ i ∧
      G.Adj hub (rim i) ∧ G.Adj hub (rim j) ∧ G.Adj hub (rim k)

/-- **Wheel-free graphs.** A simple graph $G$ is wheel-free if it has no induced wheel, that
is, no induced cycle of length at least four together with a vertex outside the cycle that is
adjacent to at least three vertices of the cycle.

Source: James Davies, arXiv:2104.05907v3, page 1, wheel definition,
https://arxiv.org/pdf/2104.05907v3. -/
def wheelFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ hasInducedWheel G

/-- **Triangle-free wheel-free graphs of large chromatic number (proposition).** This is the
proposition that for every positive integer $k$ there are a natural number $n$ and a simple
graph $G$ on the vertex set $\{0, \dots, n - 1\}$ such that $G$ contains no triangle, $G$ is
wheel-free (it has no induced wheel) and the chromatic number of $G$ is at least $k$.

Since $G$ is finite, its chromatic number is finite.

Source: Davies, arXiv:2104.05907v3, Corollary 2, page 1; the finite constructions
are given on pages 5 and 6, https://arxiv.org/pdf/2104.05907v3. -/
def largeChromaticTriangleFreeWheelFree : Prop :=
  ∀ k : ℕ, 0 < k → ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.CliqueFree 3 ∧ wheelFree G ∧ (k : ℕ∞) ≤ G.chromaticNumber

/-- **Davies's theorem on triangle-free wheel-free graphs.** For every positive integer $k$
there are a natural number $n$ and a simple graph $G$ on the vertex set $\{0, \dots, n - 1\}$
such that $G$ contains no triangle, $G$ is wheel-free (it has no induced wheel) and the
chromatic number of $G$ is at least $k$.

Source: James Davies, arXiv:2104.05907v3, Corollary 2, page 1,
https://arxiv.org/pdf/2104.05907v3. -/
public theorem_wanted largeChromaticTriangleFreeWheelFree_holds :
    largeChromaticTriangleFreeWheelFree

end MathlibExt.Combinatorics.SimpleGraph.DaviesWheelFreeChromaticWanted
