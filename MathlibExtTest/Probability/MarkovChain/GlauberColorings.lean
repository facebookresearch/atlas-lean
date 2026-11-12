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
three colors. -/
example {adj : Fin 2 → Fin 2 → Bool}
    (hadj : ∀ i j, adj i j = true → adj j i = true)
    (Δ : ℕ) (hdeg : ∀ i, (Finset.univ.filter (fun j => adj i j = true)).card ≤ Δ)
    {c d : Fin 2 → Fin 3} (hc : IsProper adj c) (hd : IsProper adj d) :
    (∑ z, (glauberCouple adj c d z).toReal * hamming z.1 z.2) ≤
      (1 - 1 / 2 + 4 * Δ / (2 * 3)) * hamming c d :=
  glauber_hamming_contract (by norm_num) (by norm_num) adj hadj Δ hdeg hc hd
