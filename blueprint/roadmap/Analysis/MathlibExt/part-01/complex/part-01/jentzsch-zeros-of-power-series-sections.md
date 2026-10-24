---
article_id: af_4aa55a6eb955a642a5cf61a3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.JentzschPowerSeriesWanted.jentzsch_zeros_of_power_series_sections
---

# Jentzsch Power Series

Jentzsch theorem on zeros of power-series sections (concept `jis_dep_a80afb88f0e7413eb0583f90`).

Source: Dilcher-Ericksen, "Polynomials Whose Coefficients Are Stern Numbers",
    Theorem 4.3 (Jentzsch).
    Exact source URL: https://cs.uwaterloo.ca/journals/JIS/VOL24/Dilcher/dilcher51.tex
    Source lines: 381-388.
    Source text SHA-256: 92c23eed1f7e91f8e2c85193cae27e57042c1e1ebe579e2be8eeb0329726fc58.
    Source object SHA-256: 72f3e8444cd0fd6b5f55e89d6427f130b294841131d89c994fe3bb2971dbb19e.

Truncation convention: the nth partial sum `∑ k = 0 ^ n, a k * z ^ k` is
    `PowerSeries.trunc (n + 1) (PowerSeries.mk a)`, since `trunc m` retains
    coefficients of degree strictly below `m`, so section `n` includes `a n`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Is Locally Uniformly Bounded On](normal-families/is-locally-uniformly-bounded-on.md)
- [Is Locally Uniformly Bounded On of forall norm le](normal-families/is-locally-uniformly-bounded-on-of-foral.md)
- [Montel](normal-families/montel.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.JentzschPowerSeries](../../../../../../sources/v2/MathlibExt.md)
