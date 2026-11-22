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
| `MathlibExt/Probability/ProbabilityMassFunction/Uniform.lean` | [`Mathlib/Probability/Distributions/Uniform.lean`](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Probability/Distributions/Uniform.lean), Mathlib `v4.34.1`, commit `d13f23b723b8a846827a245b89c10fc7d3f11612` | Narrow adaptation of the finite uniform PMF samplers retired in Mathlib 4.35. The finite-set sampler is renamed `PMF.uniformFinset`; `PMF.uniformFintype` uses the public `PMF.ofFintype` constructor with the same constant point mass. Pointwise, full-set, outer-measure and measurable-event counting formulas are retained. In pinned Mathlib, `PMF.uniformOfFintype` is a deprecated alias (since `2026-10-04`) for `MeasureTheory.Measure.uniformOfFinset : Finset α → Measure α` (`#check @PMF.uniformOfFintype` returns a `Measure`, not a `PMF`), `PMF.uniformOfFinset` does not exist, and no PMF-valued finite uniform sampler remains upstream, so these names do not replace the PMF-valued samplers here. The upstream copyright, license and authors are preserved. | Delete the local module and repoint its consumers only after pinned Mathlib provides compatible PMF-valued finite-set and finite-type samplers with the listed mass and counting APIs. Measure-valued aliases alone do not satisfy this condition. |
