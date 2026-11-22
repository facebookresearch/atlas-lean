# Binomial z-score approximation to the motif conservation score

For a natural number $N$ (occurrences of a motif) and reals $k$ (conserved occurrences) and $p$ (background conservation probability), put

$$z(N, k, p) = \frac{k - Np}{\sqrt{Np(1 - p)}},$$

with the conventions $x/0 = 0$ and $\sqrt{x} = 0$ for $x \le 0$. It is an approximation to the motif conservation score of Xie et al. (2005), not their exact score, which may differ in detail.

## Sources

- X. Xie, J. Lu, E. J. Kulbokas, T. R. Golub, V. Mootha, K. Lindblad-Toh, E. S. Lander and M. Kellis, *Systematic discovery of regulatory motifs in human promoters and 3′ UTRs by comparison of several mammals*, Nature 434 (2005), 338–345.
