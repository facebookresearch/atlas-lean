# Gilbert–Varshamov bound for linear codes

Let $F$ be a finite field with $q$ elements and let $n$, $k$ and $d \ge 1$ be natural numbers.
If

$$q^k \sum_{i=0}^{d-1} \binom{n}{i} (q-1)^i < q^n,$$

there is a [linear code](../linear-codes/linear-code.md) of length $n$ over $F$, of dimension
$k + 1$, whose [minimum distance](../linear-codes/min-dist.md) is at least $d$.

The proof starts from the zero code and applies [one greedy step](exists-extend.md) $k + 1$
times (Varshamov's argument). Guruswami, Rudra and Sudan prove the linear part of Theorem 4.2.1
with a uniformly random generator matrix instead.

## Background

- [Gilbert–Varshamov bound](exists-code-pow-le-card-mul-sum.md): the same counting for arbitrary
  codes, where the greedy code need not be linear.
- [Minimum distance equals minimum weight](../linear-codes/min-dist-eq-min-weight.md): why a
  weight bound is a distance bound for linear codes.

## Sources

- R. R. Varshamov, "Estimate of the number of signals in error correcting codes", *Doklady Akademii Nauk SSSR* 117 (1957), 739–741.
- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Theorem 4.2.1 and Section 4.2.2.
