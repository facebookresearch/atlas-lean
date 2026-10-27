---
article_id: af_07a40ea9ad8d4b5d2e67f9b6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Geometry.Euclidean.JohnsonLindenstraussWanted.johnson_lindenstrauss
---

# Johnson–Lindenstrauss lemma

**Johnson–Lindenstrauss lemma** (ATLAS N147, outer theorem): there exists a constant `C > 0`
such that for every positive real `ε`, every pair of naturals `m` and `N` with `N ≥ 2`, every
`N`-point `Finset X ⊆ EuclideanSpace ℝ (Fin m)` with `X.card = N`, and every target dimension
`d` with `(d : ℝ) > C * ε⁻¹ ^ 2 * Real.log (N : ℝ)`, there is a map
`f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d)` with
`(1 - ε) * ‖x - y‖ ≤ ‖f x - f y‖ ≤ (1 + ε) * ‖x - y‖` for all `x, y ∈ X`.

Scope notes (faithful to the ATLAS source span):
* `N ≥ 2` is an ATLAS-added exclusion carried over verbatim.
* `X.card = N` is kept as stated rather than normalized to `X.card`.
* `f` is an ordinary total map on the ambient spaces, not strengthened to a linear map.
  The ambient domain is syntactically stronger than a map defined only on `X`, but for this
  existence claim the two formulations are equivalent by restriction/extension.
* `ε > 1` is included: the source quantifies over every `ε > 0` (the `ε ≤ 1` restriction
  appears only in the intermediate lemmas, where the `ε > 1` case is discharged by the zero
  map).
* No linearity, randomness, probability distribution, or explicit value of the constant is
  asserted.

Provenance: ATLAS source-to-API map, item N147, exact module path
`Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/JohnsonLindenstrauss.lean`, source
lines 19--140, target metadata lines 832--838, report lines 1612--1638, pinned commit
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`.

Proof status: the ATLAS source proves the final theorem only through the intermediate
`jl_map_existence`, which transitively depends on the direct proof placeholder
`jl_probabilistic_existence` at source lines 23--33; the report marks that gap unjustified.
The proof below closes it with `C = 64`, a Gaussian random projection, and a union bound
over pairs of points.

Primary source: W. B. Johnson and J. Lindenstrauss, "Extensions of Lipschitz mappings into
a Hilbert space," Contemporary Mathematics 26, Conference on Modern Analysis and
Probability, American Mathematical Society (1984), 189--206, DOI 10.1090/conm/026/737400.
(The ATLAS target metadata says 1982; the publication year is 1984.)

## Depends on

This node has no prerequisites.

## Proof depends on

- [Integrable exp mul sq std Gaussian](../../../../Probability/MathlibExt/part-01/distributions/chi-square/integrable-exp-mul-sq-std-gaussian.md)
- [Mgf sq std Gaussian](../../../../Probability/MathlibExt/part-01/distributions/chi-square/mgf-sq-std-gaussian.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.JohnsonLindenstrauss](../../../../../sources/v2/MathlibExt.md)
