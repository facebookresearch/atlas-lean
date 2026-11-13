/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChain.GlauberColorings

/-- Boundary check (shape): the contraction inequality
instantiates for two proper colorings of any graph on two vertices
with three colors, with the `3Δ` constant. -/
example {G : SimpleGraph (Fin 2)} [DecidableRel G.Adj]
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (c d : G.Coloring (Fin 3)) :
    (glauberCouple G c d).expect (fun z => (hammingDist z.1 z.2 : ℝ)) ≤
      (1 - 1 / 2 + 3 * Δ / (2 * 3)) * (hammingDist (⇑c) (⇑d) : ℝ) :=
  glauber_hamming_contract (by norm_num) (by norm_num) G Δ hdeg c d

/-- The synchronous coupling has the Glauber steps as its two
marginals, for arbitrary maps. -/
example {G : SimpleGraph (Fin 2)} [DecidableRel G.Adj] {c d : Fin 2 → Fin 3} :
    (glauberCouple G c d).map Prod.fst = glauberStep G c ∧
      (glauberCouple G c d).map Prod.snd = glauberStep G d :=
  ⟨glauberCouple_map_fst G c d, glauberCouple_map_snd G c d⟩

/-- Concrete colorings `c = (0, 1)`, `d = (2, 1)` of the single-edge
graph `⊤ : SimpleGraph (Fin 2)`. -/
private def concC : (⊤ : SimpleGraph (Fin 2)).Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk ![0, 1] (by decide)

private def concD : (⊤ : SimpleGraph (Fin 2)).Coloring (Fin 3) :=
  SimpleGraph.Coloring.mk ![2, 1] (by decide)

/-- The single-edge graph has maximum degree 1. -/
example : ∀ v, (⊤ : SimpleGraph (Fin 2)).degree v ≤ 1 := by decide

/-- The concrete colorings are at Hamming distance 1. -/
example : hammingDist (⇑concC) (⇑concD) = 1 := by decide

/-- Direct evaluation of the coupled step on the concrete colorings:
the six (site, color) proposals give Hamming distances
`0, 1, 0` (site 0) and `2, 1, 2` (site 1), so the expected distance
is exactly `6 / 6 = 1`. This does not use the contraction theorem. -/
theorem glauber_concrete_expect :
    (glauberCouple ⊤ (⇑concC) (⇑concD)).expect (fun z => (hammingDist z.1 z.2 : ℝ)) = 1 := by
  rw [glauberCouple_expect]
  have h : (∑ i, ∑ col, hammingDist (glauberMove ⊤ (⇑concC) i col)
      (glauberMove ⊤ (⇑concD) i col) : ℕ) = 6 := by decide
  have hR : (∑ i, ∑ col, (hammingDist (glauberMove ⊤ (⇑concC) i col)
      (glauberMove ⊤ (⇑concD) i col) : ℝ)) = 6 := by
    exact_mod_cast h
  rw [hR]
  norm_num

/-- The `3Δ` bound is attained on the concrete example: with `n = 2`,
`q = 3`, `Δ = 1` and Hamming distance 1 the bound evaluates to `1`,
the exact expectation. -/
example :
    (glauberCouple ⊤ (⇑concC) (⇑concD)).expect (fun z => (hammingDist z.1 z.2 : ℝ)) =
      (1 - 1 / 2 + 3 * (1 : ℝ) / (2 * 3)) * 1 := by
  rw [glauber_concrete_expect]
  norm_num

/-- Any coefficient `κ < 3` in place of `3` fails on the concrete
example: the exact expectation exceeds `(1 - 1/n + κΔ/(n q))` times
the initial Hamming distance. -/
example (κ : ℝ) (hκ : κ < 3) :
    (1 - 1 / 2 + κ * 1 / (2 * 3)) * (hammingDist (⇑concC) (⇑concD) : ℝ) <
      (glauberCouple ⊤ (⇑concC) (⇑concD)).expect (fun z => (hammingDist z.1 z.2 : ℝ)) := by
  have hdist : hammingDist (⇑concC) (⇑concD) = 1 := by decide
  rw [glauber_concrete_expect, hdist]
  push_cast
  linarith
