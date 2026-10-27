---
article_id: af_17e0869d3185e3573fddf4b4
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.summatory_moebius_div_bound
---

# Explicit Mertens Bound Wanted

Explicit Mertens-type bounds for the summatory Möbius-over-`n` function:
`|∑_{n ≤ x} μ(n)/n| < 0.19/log x` for `x ≥ 33` and `< 546/(log x)^2`
for `x > 1`.

The sum ranges over `Finset.Icc 1 ⌊x⌋₊`, i.e. `n ≤ x`. These bounds
improve the author's equation (e4) (`0.2185/log x` and `726/(log x)^2`).
Spot-checked against exact partial sums at `N = 33, 40, 50, 100, 200, 500`,
all satisfying both bounds (tightest at `N = 40`: `0.0505 < 0.0515`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.ArithmeticFunction.ExplicitMertensBoundWanted](../../../../../sources/v2/WantedExt.md)
- Olivier Bordellès, "Some Explicit Estimates for the Möbius Function," Journal of Integer Sequences 18 (2015), Article 15.11.1, Theorem (label t1), items (a) and (b), lines 118–127, https://cs.uwaterloo.ca/journals/JIS/VOL18/Bordelles2/bordelles21.tex
