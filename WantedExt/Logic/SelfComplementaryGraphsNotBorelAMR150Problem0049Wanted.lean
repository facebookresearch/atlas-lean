/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Graphs on ω isomorphic to their complement (Foreman's question)

G. Barmpalias, S. Gao et al., Open problems in mathematical logic (2026), Su Gao's section, The
graph complement problem (M. Foreman, 2021): is the set `{G ∈ 2^{ω × ω} : G is a graph on ω and G ≅
G^c}` Borel?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

@[expose] public section

namespace MathlibExt.Logic.SelfComplementaryGraphsNotBorelAMR150Problem0049Wanted

/-!
Source: G. Barmpalias, S. Gao et al., Open problems in mathematical logic (2026), arXiv:2608.26628,
Su Gao's section, The graph complement problem (M. Foreman, 2021). UnsolvedMath record UM-00801037
(`AMR-150-0049`), dataset ulamai/UnsolvedMath v1.8.0.

`2^{ω × ω}` is the Cantor space `ℕ × ℕ → Bool` with the product topology, and Borel means measurable
for the Borel σ-algebra of that topology. A graph on `ω` is a symmetric irreflexive `G ⊆ ω × ω`,
`G^c = {(m, n) : m ≠ n ∧ (m, n) ∉ G}` as in the source, and `G ≅ G^c` means that some bijection `f`
of `ω` satisfies `(m, n) ∈ G ↔ (f m, f n) ∈ G^c`.
-/

/-- The points `G ∈ 2^{ω × ω}` that are graphs on `ω` isomorphic to their complement: `G` is
symmetric and irreflexive, and some bijection `f` of `ω` maps `G` onto the complement graph
`G^c = {(m, n) : m ≠ n ∧ (m, n) ∉ G}`, that is, `(m, n) ∈ G ↔ (f m, f n) ∈ G^c`. -/
def selfComplementaryGraphs : Set (ℕ × ℕ → Bool) :=
  {G | (∀ m n, G (m, n) = G (n, m)) ∧ (∀ n, G (n, n) = false) ∧
    ∃ f : ℕ ≃ ℕ, ∀ m n, G (m, n) = true ↔ (f m ≠ f n ∧ G (f m, f n) = false)}

/-- Foreman's question (2021): the set of graphs on `ω` isomorphic to their complement is a Borel
subset of the Cantor space `2^{ω × ω}`. -/
def selfComplementaryGraphsBorel : Prop :=
  @MeasurableSet (ℕ × ℕ → Bool) (borel (ℕ × ℕ → Bool)) selfComplementaryGraphs

/--
Resolved false: the problem list records that the problem was solved during the workshop, by the
theorem of Feng Li, Ruiwen Li and Ming Xiao and of Riley Thornton that the set is `Σ¹₁`-complete, so
it is not Borel. Source: G. Barmpalias, S. Gao et al., Open problems in mathematical logic (2026),
arXiv:2608.26628, Su Gao's section, The graph complement problem (M. Foreman, 2021); resolution: G.
Barmpalias, S. Gao et al., Open problems in mathematical logic (2026), arXiv:2608.26628, Su Gao's
section, theorem of Feng Li, Ruiwen Li and Ming Xiao, and of Riley Thornton, 'The problem was solved
during the workshop': the set of graphs on ω isomorphic to their complement is Σ¹₁-complete (proof
by a continuous reduction from isomorphism of countable graphs), hence not Borel,
https://arxiv.org/abs/2608.26628.
-/
public theorem_wanted selfComplementaryGraphsBorel_refuted : ¬ selfComplementaryGraphsBorel

end MathlibExt.Logic.SelfComplementaryGraphsNotBorelAMR150Problem0049Wanted
