---
article_id: af_3b71e6c6c734a74a48e06c21
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.catalan_stirling_asymptotic_expansions
---

# Catalan stirling asymptotic expansions

The two Stirling-type asymptotic expansions of the Catalan numbers, in
logarithmic form: with `C n = catalan n`, `log (C n * n * √(π * n) / 4 ^ n)`
is asymptotic to `∑_{k=1}^{m} (-1)^{k+1} ((2^{-k} - 2) B_{k+1} - k - 1) /
(k (k + 1)) n^{-k}` with remainder `o(n^{-m})` for every `m`, and
`log (C n * √(π * (n + 3/4)^3) / 4 ^ n)` is asymptotic to
`∑_{k=1}^{m} 2^{-4k-2} (4 - E_{2k}) / k (n + 3/4)^{-2k}` with remainder
`o((n + 3/4)^{-2m})` for every `m`. The sequence `E` is pinned down by the
Euler-number recurrence `E 0 = 1`, `∑_j C(n,2j) E_{n-2j} = 0` for `n > 0`
(giving `E = 1, 0, -1, 0, 5, ...`), and `bernoulli` is the Bernoulli-number
sequence. The `k = 1` term of the first expansion is `-9 / (8n)`, matching
the classical `C_n = 4^n / (√π n^{3/2}) (1 - 9/(8n) + ...)`.

Proof: The Catalan recurrence gives a logarithmic first-difference equation.
Telescoping its Bernoulli-polynomial expansion yields both all-orders formulas.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Tendsto pow mul log catalan sub bernoulli sum](tendsto-pow-mul-log-catalan-sub-bernoull.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Asymptotics.CatalanAsymptoticExpansion](../../../../../../sources/v2/MathlibExt.md)
- Neven Elezović, "Asymptotic Expansions of Central Binomial Coefficients and Catalan Numbers," Journal of Integer Sequences 17 (2014), Article 14.2.1, Catalan Stirling-type theorem (unlabeled, equation 42), lines 626–637, https://cs.uwaterloo.ca/journals/JIS/VOL17/Elezovic/elezovic5.tex
