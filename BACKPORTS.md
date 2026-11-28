# Mathlib-Derived Backports

This ledger records Mathlib-derived code temporarily maintained under
`MathlibExt/`. Each row records the exact upstream source revision, the local
adaptations, and the condition under which the backport may be removed.

## Policy

- Preserve the upstream copyright, Apache 2.0 notice, and authors block.
- Add a `BACKPORT` banner after `module` that links to this document and
  identifies the immutable upstream commit.
- Record all import-path or other local adaptations in the table below.
- Remove a backport only after the project's pinned Mathlib commit contains
  the listed upstream file and declarations. Merely upgrading beyond the
  previous pin is not sufficient.

## Ledger

| Local module | Upstream source | Adaptations | Removal condition |
|---|---|---|---|
| `MathlibExt/CategoryTheory/TrivialBundleWithFiberTerminal.lean` | [`Mathlib/CategoryTheory/MorphismProperty/TrivialBundles.lean`](https://github.com/leanprover-community/mathlib4/blob/78cb073b61a059e5450d7763216c398c12d8c89f/Mathlib/CategoryTheory/MorphismProperty/TrivialBundles.lean), PR #41750 head, blob `3a9698748c747784c77b34a8d306c6f68bf0a9bd` | Retain the actual fixed-fiber terminal-base and pullback constructions as data, rather than a mere triviality predicate. The factorization and supplied `IsPullback` witness are unchanged. | Remove only when pinned Mathlib supplies compatible data with the actual fiber `pullback p b` and its projections for the supplied terminal factorization. A Prop-valued existence result alone does not replace it. |
| `MathlibExt/Probability/ProbabilityMassFunction/Uniform.lean` | [`Mathlib/Probability/Distributions/Uniform.lean`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Probability/Distributions/Uniform.lean), Mathlib `v4.34.1`, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` | Narrow adaptation of the finite uniform PMF samplers retired in Mathlib 4.35. The finite-set sampler is renamed `PMF.uniformFinset`; `PMF.uniformFintype` uses the public `PMF.ofFintype` constructor with the same constant point mass. Pointwise, full-set, outer-measure and measurable-event counting formulas are retained. In pinned Mathlib, `PMF.uniformOfFintype` is a deprecated alias (since `2026-10-04`) for `MeasureTheory.Measure.uniformOfFinset : Finset α → Measure α` (`#check @PMF.uniformOfFintype` returns a `Measure`, not a `PMF`), `PMF.uniformOfFinset` does not exist, and no PMF-valued finite uniform sampler remains upstream, so these names do not replace the PMF-valued samplers here. The upstream copyright, license and authors are preserved. | Delete the local module and repoint its consumers only after pinned Mathlib provides compatible PMF-valued finite-set and finite-type samplers with the listed mass and counting APIs. Measure-valued aliases alone do not satisfy this condition. |
| `MathlibExt/AlgebraicTopology/SimplicialSet/StdSimplexCompat.lean` | [`Mathlib/AlgebraicTopology/SimplicialSet/StdSimplex.lean`](https://github.com/leanprover-community/mathlib4/blob/e09070f786c9fc0a688e6239d71230b618b045ff/Mathlib/AlgebraicTopology/SimplicialSet/StdSimplex.lean), Mathlib PR #42435 head `e09070f786c9fc0a688e6239d71230b618b045ff`, blob `01377b85904978d402c830501e4615606021df8c` | Retain the upstream copyright, Apache 2.0 notice and authors. At the pinned Mathlib v4.36.0 commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`, eight local declarations remain: two standard-simplex ordinal-coordinate equations, representable-isomorphism Yoneda evaluation, the constant-vertex degeneracy equation, and `ofSimplexRepresentableBy` with its identity and two inclusion equations. The five Edge/CompStruct face equations already come from the pin. The redundant local `yonedaEquiv_symm_map` is removed in favor of the native `yonedaEquiv_symm_naturality_left`. Construct representability through native `Functor.RepresentableBy.equivUliftYonedaIso` from `asIso (toOfSimplex x)` and use the pinned identity/Yoneda equations for normalization; these are local proof adaptations, not a verbatim proof copy. | Remove the local module only when the pin supplies the eight surviving interfaces, or all concrete consumers have migrated to compatible native constructions and equations. Imported Edge/CompStruct equations need no local backport. The library uses a glob; no generated `MathlibExt.lean` root is involved. |
