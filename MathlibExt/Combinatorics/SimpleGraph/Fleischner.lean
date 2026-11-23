/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity

import MathlibExt.Combinatorics.SimpleGraph.FleischnerStrong
import MathlibExt.Combinatorics.SimpleGraph.Square

/-!
# Fleischner's theorem

The proof follows Georgakopoulos's strengthened vertex-rooted induction.
-/


namespace MetaMathlibExt

@[expose] public section

/-- **Fleischner's theorem.** Let $G$ be a finite simple graph that is 2-vertex-connected, that is,
$G$ has at least three vertices and stays connected after deleting at most one vertex. Let $H$ be
the square of $G$: the graph on the same vertices in which two distinct vertices are adjacent if
and only if they are adjacent in $G$ or have a common neighbour in $G$. Then $H$ is Hamiltonian:
it has a cycle that passes through every vertex exactly once.

Proves `Wanted` entry `fleischner`.

Source: Herbert Fleischner, "The Square of Every Two-Connected Graph Is Hamiltonian," Journal of Combinatorial Theory, Series B 16 (1974), 29–34, DOI 10.1016/0095-8956(74)90091-4, https://doi.org/10.1016/0095-8956(74)90091-4.
Proof: the strengthened vertex-rooted induction of A. Georgakopoulos, "A short proof of
Fleischner's theorem", Discrete Math. 309 (2009), 6632–6634.
-/
theorem fleischner : ∀ {V : Type*} [Fintype V] (G H : SimpleGraph V),
    G.IsVertexConnected 2 →
    (∀ u v : V, H.Adj u v ↔ (u ≠ v ∧ (G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v))) →
    @SimpleGraph.IsHamiltonian V (fun a b => Classical.propDecidable _) _ H := by
  intro V _ G H hG hH
  rw [SimpleGraph.eq_square_iff.mpr hH]
  classical
  intro _
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by
    have := hG.card_gt
    omega)
  let x : V := Classical.choice hV
  obtain ⟨p, hp, _, _⟩ := hG.hasStrongSquareCycle x
  exact ⟨x, p, hp⟩

end

end MetaMathlibExt
