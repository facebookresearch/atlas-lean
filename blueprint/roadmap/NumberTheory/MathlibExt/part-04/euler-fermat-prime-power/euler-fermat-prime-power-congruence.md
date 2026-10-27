---
article_id: af_014de63d5c45080dd73dffca
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Nat.euler_fermat_prime_power_congruence
---

# Euler fermat prime power congruence

For a positive natural `a`, a prime `p`, and `1 ≤ r`,
`a ^ (p ^ r)` is congruent to `a ^ (p ^ (r - 1))` modulo `p ^ r`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Euler fermat prime power congruence general](euler-fermat-prime-power-congruence-gene.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.EulerFermatPrimePower](../../../../../sources/v2/MathlibExt.md)
- G. Everest, A. J. van der Poorten, Y. Puri, and T. Ward, "Integer Sequences and Periodic Points," Journal of Integer Sequences 5 (2002), Article 02.2.3, Corollary `eulerfermat`; public TeX: `https://cs.uwaterloo.ca/journals/JIS/VOL5/Ward/ward2.tex` (retrieved TeX SHA-256: `d0ff10fc1e4f5b6922a42bb14376c57e35883ea93f8b279c6a38f0b09a84ea54`). Proves `Wanted` entry `euler_fermat_prime_power_congruence`. It follows from `euler_fermat_prime_power_congruence_general`; the hypothesis `ha` is unused and keeps the source's shape.
