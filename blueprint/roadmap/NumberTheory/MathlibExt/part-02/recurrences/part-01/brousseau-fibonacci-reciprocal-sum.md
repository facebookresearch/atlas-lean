---
article_id: af_c831e7b90ba174f4de50509f
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.brousseau_fibonacci_reciprocal_sum
---

# Brousseau Fibonacci Reciprocal

Brousseau's Formula (6): the `n = 1` specialization of equation `equ.l14z6cr`.

Index translation: the source summation index `K ≥ 1` is represented by the Lean index
`k = K - 1`, so the sign becomes `(-1)^k`, and `2K+q`, `F_K`, and `F_{K+q}` become
`2 * (k + 1) + q`, `Nat.fib (k + 1)`, and `Nat.fib (k + 1 + q)` respectively. The finite
sum remains over `1 ≤ k ≤ q`, so its natural subtraction `k - 1` is exact. At source
parameter `n = 1`, the condition "`q` even or `nq` odd" is exhaustive for positive `q`,
so no parity hypothesis remains.
Proves `Wanted` entry `brousseau_fibonacci_reciprocal_sum`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.BrousseauFibonacciReciprocal](../../../../../../sources/v2/MathlibExt.md)
- Kunle Adegoke, "Generalizations of the Reciprocal Fibonacci-Lucas Sums of Brousseau," Journal of Integer Sequences 21 (2018), `https://cs.uwaterloo.ca/journals/JIS/VOL21/Adegoke/ade3.tex`, live and bundled source-file SHA-256 `8feb3648f4ab8f2da4d383821f763b4b57316a8f46343082a2c0d7682912f5d7`; controlling theorem, equation, and specialization at lines 1135–1148 with exact-span SHA-256 under LF joining without a terminal LF `360a38704aab45f8e89f64fb8ffc5f865c5da5316796e5ec28c650318b343dd1`; original reference: Brother Alfred Brousseau, "Fibonacci-Lucas Infinite Series — Research Topic," Fibonacci Quarterly 7 (1969), 211–217, Formula (6), cited at source line 1414; task id: `jis_grounded_50e651872ff01364d67794b1__brousseau_fibonacci_reciprocal_sum`.
