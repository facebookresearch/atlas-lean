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

/-- An induced cycle of length at least four together with an external hub
adjacent to at least three rim vertices. The hub may have further rim neighbours.
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

/-- The graph contains no induced wheel in Davies's three-neighbour sense.
Source: James Davies, arXiv:2104.05907v3, page 1, wheel definition,
https://arxiv.org/pdf/2104.05907v3. -/
def wheelFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ hasInducedWheel G

/-- The complete finite-graph existence assertion in Davies's Corollary 2.
The witnesses are finite simple graphs, enumerated by `Fin n`. Triangle-freeness
is Mathlib's `CliqueFree 3`; its extended-natural chromatic number is finite
for these vertex types. The threshold is any positive integer.
Source: Davies, arXiv:2104.05907v3, Corollary 2, page 1; the finite constructions
are given on pages 5 and 6, https://arxiv.org/pdf/2104.05907v3. -/
def largeChromaticTriangleFreeWheelFree : Prop :=
  ∀ k : ℕ, 0 < k → ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.CliqueFree 3 ∧ wheelFree G ∧ (k : ℕ∞) ≤ G.chromaticNumber

/-- Known in the cited paper; the general Lean construction and proof are
requested here. This theorem request does not supply or assume that proof.
Source: James Davies, arXiv:2104.05907v3, Corollary 2, page 1,
https://arxiv.org/pdf/2104.05907v3. -/
public theorem_wanted largeChromaticTriangleFreeWheelFree_holds :
    largeChromaticTriangleFreeWheelFree

end MathlibExt.Combinatorics.SimpleGraph.DaviesWheelFreeChromaticWanted
