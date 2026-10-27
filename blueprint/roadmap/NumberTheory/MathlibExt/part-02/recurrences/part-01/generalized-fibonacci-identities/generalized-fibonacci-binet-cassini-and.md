---
article_id: af_15a339fe07717c28e7ff0048
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.generalizedFibonacci_binet_cassini_and_ratio_limit
---

# Generalized Fibonacci binet cassini and ratio limit

Binet form, mixed Fibonacci identity, Cassini-type identity, and ratio limit
for the generalized Fibonacci sequence `W_{p,n}` with `W 0 = a`, `W 1 = b`
and `W (k+2) = p * W (k+1) + W k`; `F` is the `p`-Fibonacci case.

`Δ = a^2 + p*a*b - b^2`; `α` and `β` are the roots `(p ± √(p^2+4))/2`.
The four parts are also stated separately, each with only the hypotheses it needs:
`generalizedFibonacci_binet`, `generalizedFibonacci_mixed_identity` (for all `m n : ℤ`, so
`0 ≤ m` is not used), `generalizedFibonacci_cassini` and `generalizedFibonacci_tendsto_ratio`.
Proves `Wanted` entry `generalizedFibonacci_binet_cassini_and_ratio_limit`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Generalized Fibonacci binet](generalized-fibonacci-binet.md)
- [Generalized Fibonacci cassini](generalized-fibonacci-cassini.md)
- [Generalized Fibonacci mixed identity](generalized-fibonacci-mixed-identity.md)
- [Generalized Fibonacci tendsto ratio](generalized-fibonacci-tendsto-ratio.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.GeneralizedFibonacciIdentities](../../../../../../../sources/v2/MathlibExt.md)
- Abdelhak Taane, Ihab-Eddine Djellas, and Mohammed Mekkaoui, "Total Positivity of Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers," Journal of Integer Sequences 29 (2026), Article 26.2.5, preliminary-results lemma, lines 192–200, https://cs.uwaterloo.ca/journals/JIS/VOL29/Djellas/djellas7.tex
