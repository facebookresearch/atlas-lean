/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MarkovChain.GlauberColorings

/-- Boundary check (shape): the contraction inequality
instantiates for two proper colorings of a two-vertex graph with
three colors, with the `3Δ` constant. -/
example {adj : Fin 2 → Fin 2 → Bool}
    (hadj : ∀ i j, adj i j = true → adj j i = true)
    (Δ : ℕ) (hdeg : ∀ i, (Finset.univ.filter (fun j => adj i j = true)).card ≤ Δ)
    {c d : Fin 2 → Fin 3} (hc : IsProper adj c) (hd : IsProper adj d) :
    (∑ z, (glauberCouple adj c d z).toReal *
      ((hammingDist z.1 z.2 : ℕ) : ℝ)) ≤
      (1 - 1 / 2 + 3 * Δ / (2 * 3)) * ((hammingDist c d : ℕ) : ℝ) :=
  glauber_hamming_contract (by norm_num) (by norm_num) adj hadj Δ hdeg hc hd

/-- The synchronous coupling has the Glauber steps as its two
marginals, for arbitrary colorings. -/
example {adj : Fin 2 → Fin 2 → Bool} {c d : Fin 2 → Fin 3} :
    (glauberCouple adj c d).map Prod.fst = glauberStep adj c ∧
      (glauberCouple adj c d).map Prod.snd = glauberStep adj d :=
  ⟨glauberCouple_map_fst adj c d, glauberCouple_map_snd adj c d⟩

/-- Concrete single-edge graph on two vertices. -/
private def singleEdge : Fin 2 → Fin 2 → Bool :=
  fun i j => decide (i ≠ j)

/-- Concrete proper colorings `c = (0, 1)`, `d = (2, 1)` of the
single-edge graph. -/
private def concC : Fin 2 → Fin 3 := ![0, 1]

private def concD : Fin 2 → Fin 3 := ![2, 1]

/-- The concrete colorings are proper for the single-edge graph. -/
example : IsProper singleEdge concC := by unfold IsProper; decide

example : IsProper singleEdge concD := by unfold IsProper; decide

/-- The single-edge graph is symmetric and has degree at most 1. -/
example : (∀ i j, singleEdge i j = true → singleEdge j i = true) ∧
    ∀ i, (Finset.univ.filter (fun j => singleEdge i j = true)).card ≤ 1 := by
  exact ⟨by decide, by decide⟩

/-- The concrete colorings are at Hamming distance 1. -/
example : hammingDist concC concD = 1 := by decide

/-- Concrete contraction check: on the single-edge graph with
`Δ = 1`, the coupled expectation is at most the `3Δ` bound,
which is exactly `1` here. -/
example :
    (∑ z, (glauberCouple singleEdge concC concD z).toReal *
      ((hammingDist z.1 z.2 : ℕ) : ℝ)) ≤ 1 := by
  have hc : IsProper singleEdge concC := by unfold IsProper; decide
  have hd : IsProper singleEdge concD := by unfold IsProper; decide
  have hadj : ∀ i j, singleEdge i j = true → singleEdge j i = true := by decide
  have hdeg : ∀ i, (Finset.univ.filter (fun j => singleEdge i j = true)).card ≤ 1 := by decide
  have h := glauber_hamming_contract (n := 2) (q := 3) (by norm_num) (by norm_num)
    singleEdge hadj 1 hdeg hc hd
  have hdist : hammingDist concC concD = 1 := by decide
  rw [hdist] at h
  norm_num at h
  exact h
