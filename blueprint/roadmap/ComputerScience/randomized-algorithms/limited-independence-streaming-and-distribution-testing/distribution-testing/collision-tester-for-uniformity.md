# The collision tester for uniformity

Draw $k$ samples from $p$ on $n$ points and count the colliding pairs $C$. Accept iff $C < \binom{k}{2}\frac{1 + 3\varepsilon^2}{n}$. If $k \ge 800\sqrt n/\varepsilon^2$, this accepts the uniform distribution and rejects every $p$ with $d_{TV}(p, U) \ge \varepsilon$, each with probability at least $3/4$; hence $k = O(\sqrt n / \varepsilon^2)$ samples suffice.

## Proof sketch

$\mathbb{E}[C] = \binom{k}{2}\|p\|_2^2$, and $\|p\|_2^2 = 1/n$ for uniform while $\|p\|_2^2 \ge (1 + 4\varepsilon^2)/n$ when $d_{TV}(p, U) \ge \varepsilon$ (Cauchy–Schwarz). The variance bound $\mathrm{Var}[C] \le k^2\|p\|_2^2 + k^3(\|p\|_3^3 - \|p\|_2^4)$ and Chebyshev's inequality separate the two cases at the stated sample size; this is the $\ell_2$ tester of Diakonikolas et al. with $\ell_2$ proximity $2\varepsilon/\sqrt n$.

## Depends on

- [Sample-based distribution testers](sample-based-distribution-testers.md)

## Sources

- O. Goldreich and D. Ron, "On Testing Expansion in Bounded-Degree Graphs", ECCC technical report TR00-020, 2000.
- I. Diakonikolas, T. Gouleakis, J. Peebles and E. Price, "Collision-Based Testers are Optimal for Uniformity and Closeness", Chicago Journal of Theoretical Computer Science 2019, Theorem 1 and Lemmas 2-7 (stated for $\|p - U\|_2^2 \ge \varepsilon'^2/n$ with $3200\sqrt n/\varepsilon'^2$ samples).
- C. L. Canonne, "A Survey on Distribution Testing: Your Data is Big. But is it Blue?", Theory of Computing Graduate Surveys 9, 2020.
