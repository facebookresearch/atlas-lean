---
article_id: af_601d90fed933dab8a6c6eeff
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.gessel_bernoulli_number_identity
---

# Gessel Identity

Gessel's Bernoulli-number identity (Belbachir–Rahmani form of Gessel's identity).

`bernoulli` is Mathlib's `bernoulli`, with `B₁ = -1/2`.

The two right-hand exponents are stated with rational `zpow` and integer
exponents `((j : ℤ) + (n : ℤ) - 1)` and `((n : ℤ) + (r : ℤ) - (j : ℤ))`
rather than `ℕ` subtraction: at `n = 0` the endpoints `j = 0` and `j = r + 1`
give exponent `-1`, which `ℕ` subtraction would silently truncate to `0`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Bernoulli.GesselIdentity](../../../../../sources/v2/MathlibExt.md)
- Redha Chellal and Farid Bencherif, *An Identity for Generalized Bernoulli Polynomials*, Journal of Integer Sequences 23 (2020), Article 20.11.2, formula `t5` (the special case `ℓ = n` with `r` odd), lines 142–149, <https://cs.uwaterloo.ca/journals/JIS/VOL23/Chellal/chellal7.tex>. Quoted there from H. Belbachir and M. Rahmani, *On Gessel-Kaneko's identity for Bernoulli numbers*, Appl. Anal. Discrete Math. 7 (2013), 1–10. Original: I. M. Gessel, *Applications of the classical umbral calculus*, Algebra Universalis 49 (2003), 397–434.
