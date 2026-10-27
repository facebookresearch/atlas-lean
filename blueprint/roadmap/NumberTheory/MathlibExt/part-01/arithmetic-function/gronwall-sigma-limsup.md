---
article_id: af_a7ac1692fcd5f469ed26104a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsupWanted.gronwall_sigma_limsup
---

# Gronwall's theorem

**Gronwall's theorem** (maximal order of the sum-of-divisors function): the `limsup`
at `Filter.atTop` of `σ(n) / (n * log (log n))` equals `Real.exp
Real.eulerMascheroniConstant`, i.e. `e ^ γ`. Source: S. Nazardonyavi and S. Yakubovich,
"Extremely Abundant Numbers and the Riemann Hypothesis," Journal of Integer Sequences 17
(2014), Article 14.2.8, lines 98–111,
https://cs.uwaterloo.ca/journals/JIS/VOL17/Nazar/nazar4.tex (live source SHA-256
`6854eacdc72e1e5a005b005552942d6d7cfa7a41d7892c0f61bb2b1886e1d7c5`); original
attribution: T. H. Gronwall, "Some asymptotic expressions in the theory of numbers,"
Transactions of the AMS 14 (1913), 113–122. Totalization note: `σ`, division, and the
logarithms are total Lean functions, so the finitely many small natural inputs where
`n * log (log n)` is nonpositive or zero merely contribute finitely many values and do
not affect the `limsup` at `Filter.atTop`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsup](../../../../../sources/v2/MathlibExt.md)
