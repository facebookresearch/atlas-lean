# Expected order of saturated RNA secondary structures

Write an RNA secondary structure of size $n$ in dot-bracket form. It is *saturated* if no further base pair (arc) can be added without violating the secondary-structure conditions; the generating function $S(z)$ of saturated structures satisfies

$$
-S(z)^3 z^4 - S(z)^2 z^2 (z^2 - 2) + S(z)(z^2 - 1) + z(1+z) = 0 .
$$

The *order* of a structure $s$ (Waterman) is the number $p$ of rounds needed to reach the empty word when, in each round, all maximal substrings of the form $(^k)^k$ of $\phi(s)$ are deleted in parallel, where $\phi$ erases unpaired positions; it measures the balanced nesting depth of hairpin loops and is a Horton–Strahler-type parameter. Let $\xi_n$ be the order of a uniformly random saturated structure of size $n$.

**Theorem.**

$$
\mathbb{E}\,\xi_n = \log_4 n \cdot \Big(1 + O\Big(\frac{\log_2 n}{n}\Big)\Big),
$$

and for every $\beta > 0$ and $0 \le x \le (\tfrac12 - \beta)\log_4 n$,

$$
\mathbb{P}\big(|\xi_n - \mathbb{E}\,\xi_n| \ge x\big) = O(2^{-x}).
$$

## Expansion

One derives a functional equation for the generating function $S_p(z)$ of saturated structures of order at least $p$, and writes the expected order as $\mathbb{E}\,\xi_n = \sum_{p \ge 1} [z^n]S_p(z)/[z^n]S(z)$; singularity analysis of the $S_p$ near the dominant singularity of $S$ shows that the terms are close to $1$ up to $p \approx \log_4 n$ and decay geometrically beyond. A transfer theorem on Hankel contours, $f(z) = O(\sqrt{1-z}\,\log(1/(1-z)))$ implying $[z^n]f = O(n^{-3/2}\log n)$, controls the error terms. The result matches the expected order of unrestricted secondary structures, so enforcing saturation, which lengthens stacking regions, does not change the overall shape measured by the order.

## Sources

- Emma Yu Jin and Markus E. Nebel, *The Expected Order of Saturated RNA Secondary Structures*, arXiv:1107.3033, Theorems 1 and 2 (Section 2) and Theorems 3–5 (Section 3). <https://doi.org/10.48550/arXiv.1107.3033> Published version: 2012 Proceedings of the Ninth Workshop on Analytic Algorithmics and Combinatorics (ANALCO) (2012) 84–91, <https://doi.org/10.1137/1.9781611973020.11>.
