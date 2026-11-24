# Admissibility needs only the primes up to the size of the set

A finite set $H$ of integers is [admissible](is-admissible-finset.md) if and only if, for every prime $p \le \#H$, some residue class modulo $p$ contains no element of $H$. A prime $p > \#H$ never needs checking: $\#H$ integers meet at most $\#H < p$ residue classes modulo $p$.

This is the remark before display (1.6) of Goldston, Pintz and Yıldırım: the condition "is immediately true for all primes $p > k$, so to test this condition we need only to examine small primes". Maynard (2015) uses the same count in the proof of Theorem 1.1 to show that the $k$ primes following $k$ form an admissible set.

Degenerate cases: for the empty set and for one-element sets there is no prime $p \le \#H$, so they are admissible.

## Sources

- D. A. Goldston, J. Pintz and C. Y. Yıldırım, "Primes in tuples I", *Ann. of Math.* 170 (2009), 819–862; theorem and display numbers are those of arXiv:math/0508185v1 (10 Aug 2005).
- J. Maynard, "Small gaps between primes", *Ann. of Math.* 181 (2015), 383–413; theorem and display numbers are those of arXiv:1311.4600v3 (28 Oct 2019).
