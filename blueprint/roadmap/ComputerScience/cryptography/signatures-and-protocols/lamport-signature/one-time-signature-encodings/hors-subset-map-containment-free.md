# The HORS subset map is containment free

If $2^{v} \le \binom{n}{\ell}$, then the map sending a $v$-bit message (read as an integer $m < 2^v$) to the $m$-th $\ell$-element subset of $\{1, \dots, n\}$ in a fixed ranking of $\ell$-subsets is injective, takes values of size exactly $\ell$, is computable in polynomial time (by combinatorial unranking), and is containment free.

## Proof sketch

Distinct sets of equal size $\ell$ are never contained in one another; unranking is a bijection between $\{0, \dots, \binom{n}{\ell} - 1\}$ and the $\ell$-subsets.

## Depends on

- [Containment-free and domination-free encodings](containment-and-domination-free-encodings.md)

## Sources

- L. Reyzin and N. Reyzin, "Better than BiBa: Short One-Time Signatures with Fast Signing and Verifying", Information Security and Privacy (ACISP 2002), LNCS 2384, 2002.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
