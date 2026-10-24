---
article_id: af_bbc3e4b3540d9610af7afe9c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.garabedian_genocchi_formula
---

# Garabedian genocchi formula

Garabedian's Bernoulli-number identity in Stirling form: for `n ≥ 1`,
`2 * (1 - 2 ^ n) * B n` equals `n` times the signed sum of
`(-1) ^ (n - k) * (k - 1)! * S(n, k) / 2 ^ (k - 1)` over `1 ≤ k ≤ n`,
with `B = bernoulli` and `S = Nat.stirlingSecond`.

Since `k ∈ Finset.Icc 1 n`, the natural subtractions `n - k` and `k - 1`
are genuine differences.

It follows from `garabedian_genocchi_formula_general`; the hypothesis `hn` is unused and
keeps the source's shape.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Garabedian genocchi formula general](garabedian-genocchi-formula-general.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.GarabedianBernoulliStirling](../../../../../../../sources/v2/MathlibExt.md)
- Schehrazade Zerroukhat and Laala Khaldi, "A Note on Explicit Formulas for Bernoulli and Genocchi Numbers," Journal of Integer Sequences 28 (2025), Article 25.6.7, equation (g19), lines 188–191 of the official TeX, <https://cs.uwaterloo.ca/journals/JIS/VOL28/Zerroukhat/zerrou3.tex>, which displays `2(1-2^n)B_n = G_n = n ∑ ...` and notes Garabedian's formula is equivalent to it; this module formalizes the outer (Bernoulli-to-sum) equality. Original: H. L. Garabedian, "A new formula for the Bernoulli numbers," Bull. Amer. Math. Soc. 46 (1940), 531–533.
