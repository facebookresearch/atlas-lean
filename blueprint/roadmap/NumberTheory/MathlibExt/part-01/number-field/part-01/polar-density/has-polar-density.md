---
article_id: af_92e3b9ff5854d635734722c7
declaration: def
origin: cited
statement: formalized
lean: NumberField.Set.HasPolarDensity
---

# Has Polar Density

Polar density of a set of height-one primes, via a meromorphic continuation.

`HasPolarDensity S ρ` asserts the existence of a positive exponent `n : ℕ+`, a
pole order `m : ℤ`, and an actual meromorphic continuation `F : ℂ → ℂ` such that
`F` is meromorphic at `1`, agrees with the pointwise `n`-th power of the partial
Dedekind zeta function on the right-half-plane germ at `1`, has
`meromorphicOrderAt F 1 = -m`, and `ρ = m / n`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Partial Dedekind Zeta](../partial-dedekind-zeta.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.NumberField.PolarDensity](../../../../../../../sources/v2/MathlibExt.md)
