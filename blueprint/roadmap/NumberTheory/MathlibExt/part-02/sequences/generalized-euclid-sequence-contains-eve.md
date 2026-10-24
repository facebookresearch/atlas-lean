---
article_id: af_c114a201599fe8e45d8bed49
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.generalized_euclid_sequence_contains_every_prime
---

# Generalized Euclid Sequence

For any finite set `P` of primes there is a generalized Euclid sequence
with seed `P` (each new term a prime divisor of
`∏_{i ∈ I} p_i + ∏_{i ∉ I} p_i` for some `I`) containing every prime.

The source's construction: for primes `p_1, …, p_k` and any
`I ⊆ {1, …, k}`, `N_I = ∏_{i ∈ I} p_i + ∏_{i ∉ I} p_i` is coprime to
the previous product, so a prime divisor of `N_I` is always new; the
sequence is zero-indexed here with the first `P.card` terms enumerating
the seed. This is an existence claim over all choices of `I` and prime
divisor, unlike the open Euclid–Mullin conjecture about one specific
sequence.

Proof: Booker's residue-set route, with an elementary squarefree count in place of Rogers'
density bound and Jacobi-sum character-sum bounds in place of the Hasse and Weil bounds.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Sequences.GeneralizedEuclidSequence](../../../../../sources/v2/MathlibExt.md)
- Andrew R. Booker, "A Variant of the Euclid-Mullin Sequence Containing Every Prime," Journal of Integer Sequences 19 (2016), Article 16.6.4, Theorem (label t:main), lines 132–136, https://cs.uwaterloo.ca/journals/JIS/VOL19/Booker/book3.tex
