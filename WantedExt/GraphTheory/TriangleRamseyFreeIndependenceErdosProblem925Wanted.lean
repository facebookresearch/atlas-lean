/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Independent sets in graphs that are not Ramsey for the triangle (Erdős Problem 925)

Erdős Problem 925: is there a constant `δ > 0` such that, for all large `n`, if `G` is a graph on
`n` vertices which is not Ramsey for `K₃` (there exists a `2`-colouring of the edges of `G` with no
monochromatic triangle) then `G` contains an independent set of size `≫ n^{1/3 + δ}`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MathlibExt.GraphTheory.TriangleRamseyFreeIndependenceErdosProblem925Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #925, https://www.erdosproblems.com/925 (status
DISPROVED). UnsolvedMath record UM-30007092 (`EP-925`), dataset ulamai/UnsolvedMath v1.8.0.

A `2`-colouring of the edges with no monochromatic triangle amounts to writing `G = G₁ ⊔ G₂` with
`G₁` and `G₂` triangle-free (`CliqueFree 3`). `≫ n^{1/3 + δ}` means at least `c n^{1/3 + δ}` for a
constant `c > 0`; the claim is that some `δ` and `c` work for all large `n`. formal-conjectures has
no statement of this problem.
-/

/-- Erdős Problem 925: there are `δ > 0` and `c > 0` such that for all large `n`, every graph on `n`
vertices whose edges can be coloured with two colours without a monochromatic triangle (that is,
which is the union of two triangle-free graphs) has an independent set of size at least
`c n^{1/3 + δ}`. -/
def nonRamseyTriangleLargeIndependentSet : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ G : SimpleGraph (Fin n),
    (∃ G₁ G₂ : SimpleGraph (Fin n), G₁.CliqueFree 3 ∧ G₂.CliqueFree 3 ∧ G = G₁ ⊔ G₂) →
      ∃ s : Finset (Fin n), G.IsIndepSet (s : Set (Fin n)) ∧
        c * (n : ℝ) ^ ((1 : ℝ) / 3 + δ) ≤ s.card

/--
Resolved false: the question asks whether `R(3, 3, m) ≪ m^{3 - c}` for some `c > 0`
(erdosproblems.com/925), and Alon and Rödl proved `R(3, 3, m) ≥ m³ / (log m)^{4 + o(1)}`: there are
graphs on `m^{3 - o(1)}` vertices, each the union of two triangle-free graphs, with no independent
set of size `m`, so no `δ > 0` and `c > 0` work. Source: T. F. Bloom, Erdős Problems, Problem #925,
https://www.erdosproblems.com/925 (status DISPROVED); resolution: N. Alon and V. Rödl, Sharp bounds
for some multicolor Ramsey numbers, Combinatorica (2005), 125-141, Section 1, (1) with k = 2: r(K₃,
K₃, K_m) = Θ(m³ polylog m); erdosproblems.com/925: the question asks whether R(3, 3, m) ≪ m^{3-c}
for some c > 0, disproved by the bound m³/(log m)^{4+o(1)} ≪ R(3, 3, m),
http://tau.ac.il/~nogaa/PDFS/arodl4.pdf.
-/
public theorem_wanted nonRamseyTriangleLargeIndependentSet_refuted :
    ¬ nonRamseyTriangleLargeIndependentSet

end MathlibExt.GraphTheory.TriangleRamseyFreeIndependenceErdosProblem925Wanted
