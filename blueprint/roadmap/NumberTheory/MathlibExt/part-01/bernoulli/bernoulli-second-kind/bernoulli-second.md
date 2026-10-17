---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.bernoulliSecond
---

# Bernoulli Second

Bernoulli number of the second kind `Bₙ^*`: `n!` times coefficient
`n` of `bernoulliSecondPowerSeries`, i.e. the
exponential-generating-function normalization of
`t / log (1 + t) = ∑ₙ Bₙ^* * t ^ n / n!` (Roman's normalization;
`B₀^* = 1`, `B₁^* = 1 / 2`, `B₂^* = -1 / 6`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Bernoulli Second Power Series](bernoulli-second-power-series.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Bernoulli.BernoulliSecondKind](../../../../../../sources/v2/MathlibExt.md)
