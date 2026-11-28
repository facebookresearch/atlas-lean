# Critical Probability eq half of self Dual Assembly

Abstract assembly lemma: `p_c(ℤ²) = 1/2` for bond percolation follows from the
self-duality computation together with the assumed substantive inputs of Kesten's theorem
(Kesten, "The critical probability of bond percolation on the square lattice equals 1/2",
1980). This is **not** Kesten's theorem: the hypotheses below are assumed, not proved.

The hypotheses that carry the mathematical content of Kesten's theorem are assumed:
* `hCorLowerBound` (with `hbxp`): `θ(1/2) = 0`. This is Harris's theorem; in the literature it
  follows from RSW (open circuits in disjoint annuli) and gives `1/2 ≤ p_c`.
* `hSharpThreshold`: for every `p < p_c`, `ℙ_p(boxFam n) → 0`. This is the subcritical decay of
  crossing probabilities (Kesten's sharp-threshold argument, or Menshikov / Aizenman–Barsky
  exponential decay); it gives `p_c ≤ 1/2`.
* `hdich`, `hRpres`, `hHm`: `boxFam` is an exactly self-dual family, i.e. its complement is its
  preimage under a `ℙ_{1/2}`-preserving map `R ∘ dualConfig`. In the literature this is planar
  duality for the left–right crossing of an `(n + 1) × n` rectangle; no family satisfying `hdich`
  is constructed in Atlas.
What is proved is the self-duality computation `ℙ_{1/2}(boxFam n) = 1/2` and the order argument.

`hbxp` enters only through `hCorLowerBound`.

See also `StatMech.TwoDim.kesten_pc_le_half`, a conditional upper-half form stated with an
abstract crossing function.
