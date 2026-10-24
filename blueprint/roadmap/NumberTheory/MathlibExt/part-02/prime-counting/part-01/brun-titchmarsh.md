---
article_id: af_c12b4c0a9ac8f03eeb188cd2
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshWanted.brun_titchmarsh
---

# Brun Titchmarsh

For coprime `a` and `q`, with `1 ≤ q < X`, the inclusive residue-class
prime count satisfies
`π(X; q, a) ≤ 2X / (φ(q) log(X/q))`.

Proof: An elementary Eratosthenes sieve handles `X ≤ 20000q`. Above that
range, the weighted arithmetic large sieve is combined with explicit lower
bounds for the squarefree-totient sum and the choice
`z = ⌊√(2N/3)⌋`, where `N = ⌊X/q⌋ + 1`.

## Depends on

- [Prime Counting Mod](../part-02/residue-class/prime-counting-mod.md)

## Proof depends on

- [Arithmetic Large Sieve](arithmetic-large-sieve-progression.md)
- [Squarefree Totient Weighted](../part-02/squarefree-totient-weighted-lower.md)
- [Prime Counting Mod eq card filter range](../part-02/residue-class/prime-counting-mod-eq-card-filter-range.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarsh](../../../../../../sources/v2/MathlibExt.md)
- H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004, Theorem 6.6; quoted as equation (1) in Y. Wang and X. Zhang, arXiv:2608.19262v1.
