/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Paul Bendich
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 480, Combinatorics 493

/-!
# Contains a (c,d)-Biclique; Biclique Number

## References

* https://en.wikipedia.org/wiki/Complete_bipartite_graph (for `SimpleGraph.ContainsBiclique`)
* https://arxiv.org/pdf/1511.00270 see Section 9.4, page 23, right before the statement of Conj.
  9.4. (for `SimpleGraph.bicliqueNumber`)

## References

* https://en.wikipedia.org/wiki/Complete_bipartite_graph (for `SimpleGraph.ContainsBiclique`)
* https://arxiv.org/pdf/1511.00270 see Section 9.4, page 23, right before the statement of Conj.
  9.4. (for `SimpleGraph.bicliqueNumber`)

## References

* https://en.wikipedia.org/wiki/Complete_bipartite_graph (for `SimpleGraph.ContainsBiclique`)
* https://arxiv.org/pdf/1511.00270 see Section 9.4, page 23, right before the statement of Conj.
  9.4. (for `SimpleGraph.bicliqueNumber`)

## References

* https://en.wikipedia.org/wiki/Complete_bipartite_graph (for `SimpleGraph.ContainsBiclique`)
* https://arxiv.org/pdf/1511.00270 see Section 9.4, page 23, right before the statement of Conj.
  9.4. (for `SimpleGraph.bicliqueNumber`)

## References

* https://en.wikipedia.org/wiki/Complete_bipartite_graph (for `SimpleGraph.ContainsBiclique`)
* https://arxiv.org/pdf/1511.00270 see Section 9.4, page 23, right before the statement of Conj.
  9.4. (for `SimpleGraph.bicliqueNumber`)

## References

* https://en.wikipedia.org/wiki/Complete_bipartite_graph (for `SimpleGraph.ContainsBiclique`)
* https://arxiv.org/pdf/1511.00270 see Section 9.4, page 23, right before the statement of Conj.
  9.4. (for `SimpleGraph.bicliqueNumber`)

## References

* https://en.wikipedia.org/wiki/Complete_bipartite_graph (for `SimpleGraph.ContainsBiclique`)
* https://arxiv.org/pdf/1511.00270 see Section 9.4, page 23, right before the statement of Conj.
  9.4. (for `SimpleGraph.bicliqueNumber`)
-/

namespace MetaMathlibExt

-- Combinatorics 480: Contains a (c,d)-Biclique

/-- Let G = (V,E) be a finite simple graph and let c,d be positive integers. G contains a
(c,d)-biclique if there exist nonempty and disjoint subsets X,Y ⊂ V such that |X| = c, |Y| =d, and ∀
x ∈ X, y ∈ Y, we have (x,y) ∈ E.
-/
def _root_.SimpleGraph.ContainsBiclique {V : Type*} [Fintype V] (G : SimpleGraph V)
    (c d : ℕ) : Prop :=
  ∃ (S T : Finset V), S.card = c ∧ T.card = d ∧ Disjoint S T ∧
    ∀ a ∈ S, ∀ b ∈ T, G.Adj a b

-- Combinatorics 493: Biclique Number

/-- Let G be a finite simple graph. The biclique number ω_b(G) is the maximum positive integer t
such that G contains a K_{c,d} as a (not necessarily induced) subgraph, with 0<c,d and c +d = t.
-/
noncomputable def _root_.SimpleGraph.bicliqueNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  sSup { t : ℕ |  ∃ c d, c + d = t ∧ 0 < c ∧ 0 < d ∧ G.ContainsBiclique c d}

end MetaMathlibExt

end
