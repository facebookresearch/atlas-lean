# The collision tester for uniformity

Draw $k$ samples from $p$ on $n$ points and count the colliding pairs $C$. Accept iff $C \le \binom{k}{2}\frac{1 + 2\varepsilon^2}{n}$. If $40\sqrt n \le (k - 1)\varepsilon^2$, this is a uniformity tester with proximity $\varepsilon$; hence $k = O(\sqrt n / \varepsilon^2)$ samples suffice.

## Proof sketch

$\mathbb{E}[C] = \binom{k}{2}\|p\|_2^2$, and $\|p\|_2^2 = 1/n$ for uniform while $\|p\|_2^2 \ge (1 + 4\varepsilon^2)/n$ when $d_{TV}(p, U) \ge \varepsilon$ (Cauchy–Schwarz). A careful variance bound on $C$ and Chebyshev's inequality separate the two cases at the stated sample size.

## Depends on

- [Sample-based distribution testers](sample-based-distribution-testers.md)

## Sources

- O. Goldreich and D. Ron, "On Testing Expansion in Bounded-Degree Graphs", ECCC technical report TR00-020, 2000.
- I. Diakonikolas, T. Gouleakis, J. Peebles and E. Price, "Collision-Based Testers are Optimal for Uniformity and Closeness", Chicago Journal of Theoretical Computer Science 2019.
- C. L. Canonne, "A Survey on Distribution Testing: Your Data is Big. But is it Blue?", Theory of Computing Graduate Surveys 9, 2020.
