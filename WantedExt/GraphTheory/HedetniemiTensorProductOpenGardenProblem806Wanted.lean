/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hedetniemi's conjecture (Open Problem Garden 806)

Open Problem Garden, Hedetniemi's Conjecture (S. T. Hedetniemi): if `G` and `H` are simple finite
graphs, then `χ(G × H) = min (χ(G), χ(H))`, where `G × H` is the tensor product.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MathlibExt.GraphTheory.HedetniemiTensorProductOpenGardenProblem806Wanted

/-!
Source: Open Problem Garden, Hedetniemi's Conjecture (node 806; S. T. Hedetniemi),
http://www.openproblemgarden.org/op/hedetniemis_conjecture. UnsolvedMath record UM-00003233
(`OPG-806`), dataset ulamai/UnsolvedMath v1.8.0.

The tensor (direct, categorical) product has vertex set `V(G) × V(H)`, with `(g, h)` adjacent to
`(g', h')` iff `g g' ∈ E(G)` and `h h' ∈ E(H)` (Shitov's definition). Chromatic numbers are
Mathlib's `SimpleGraph.chromaticNumber` (values in `ℕ∞`, finite for finite graphs).
-/

/-- The tensor (direct, categorical) product `G × H`: `(g, h)` and `(g', h')` are adjacent iff
`g ~ g'` in `G` and `h ~ h'` in `H`. -/
def tensorProd {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) where
  Adj p q := G.Adj p.1 q.1 ∧ H.Adj p.2 q.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

/-- Hedetniemi's conjecture: `χ(G × H) = min (χ(G), χ(H))` for all finite simple graphs `G`, `H`. -/
def hedetniemiConjecture : Prop :=
  ∀ (V W : Type) [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W),
    (tensorProd G H).chromaticNumber = min G.chromaticNumber H.chromaticNumber

/--
Resolved false: Shitov constructs finite simple graphs `G` and `H` with `χ(G × H) < min (χ(G),
χ(H))`. (The inequality `χ(G × H) ≤ min (χ(G), χ(H))` always holds, so the conjecture asserted the
reverse inequality.) Source: Open Problem Garden, Hedetniemi's Conjecture (node 806; S. T.
Hedetniemi), http://www.openproblemgarden.org/op/hedetniemis_conjecture; resolution: Y. Shitov,
Counterexamples to Hedetniemi's conjecture, Ann. of Math. (2) 190 (2019), 663-667; arXiv:1905.02167,
main result (abstract): the chromatic number of G × H can be less than the minimum of the chromatic
numbers of finite simple graphs G and H, https://doi.org/10.4007/annals.2019.190.2.6.
-/
public theorem_wanted hedetniemiConjecture_refuted : ¬ hedetniemiConjecture

end MathlibExt.GraphTheory.HedetniemiTensorProductOpenGardenProblem806Wanted
