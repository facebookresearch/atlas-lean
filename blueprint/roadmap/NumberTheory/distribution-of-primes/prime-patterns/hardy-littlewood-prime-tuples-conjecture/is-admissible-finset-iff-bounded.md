# Bounded search form of admissibility

A finite set $H$ of integers is [admissible](is-admissible-finset.md) if and only if for every prime $p \le \#H$ there is $r \in \{0, \dots, p - 1\}$ with $h \not\equiv r \pmod p$ for all $h \in H$. Every quantifier ranges over a finite set, so admissibility can be decided by a finite computation.

For example, this finite check shows that Maynard's $5$-tuple $\{0, 2, 6, 8, 12\}$, the GPY $6$-tuple $\{0, 4, 6, 10, 12, 16\}$ and Maynard's admissible $105$-tuple of diameter $600$ are admissible, and that $\{0, 2, 4\}$ is not, since it meets every residue class modulo $3$.

## Informally uses

- [Admissibility needs only the primes up to the size of the set](is-admissible-finset-iff-forall-prime-le.md): the reduction to primes $p \le \#H$.

## Sources

- D. A. Goldston, J. Pintz and C. Y. Yıldırım, "Primes in tuples I", *Ann. of Math.* 170 (2009), 819–862; theorem and display numbers are those of arXiv:math/0508185v1 (10 Aug 2005).
- J. Maynard, "Small gaps between primes", *Ann. of Math.* 181 (2015), 383–413; theorem and display numbers are those of arXiv:1311.4600v3 (28 Oct 2019).
