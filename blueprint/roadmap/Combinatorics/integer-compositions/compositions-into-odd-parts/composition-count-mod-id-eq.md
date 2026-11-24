# Compositions with a colors on a part a and a part count in a residue class

Let $\nu(a) = a$, so that a part $a$ carries one of $a$ colors, and let $b_\nu(m, q; n)$ and $c_\nu(m, q; n)$ be the numbers of such colored compositions and colored circular compositions of $n$ whose number of parts is congruent to $q$ modulo $m$. Let $b_O$ and $c_O$ be the same counts for compositions into odd parts (one color each), and let $T(m, n, q)$ be the set of natural numbers $k$ with $k \equiv n - q \pmod m$ (the difference taken in $\mathbb{Z}$) and $k < n$. For natural numbers $m$, $q$ and $n$ with $q < m$ and $n \ge 1$:

$$b_\nu(m, q; n) = b_O(2m, 2q; 2n) = \sum_{k \in T(m, n, q)} \binom{2n - k - 1}{k},$$

in $\mathbb{N}$, and

$$c_\nu(m, q; n) = c_O(2m, 2q; 2n), \qquad c_\nu(m, q; n) = \sum_{k \in T(m, n, q)} \frac{2n}{2n - k} \binom{2n - k}{k},$$

the first in $\mathbb{N}$ and the second in $\mathbb{Q}$.

## Sources

- Joshua P. Bowman, *Compositions with an Odd Number of Parts, and Other Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6, Theorem 17.
