# Thresholds for perfect matchings and F-factors via spreadness

For fixed $k \ge 2$, the threshold for the random $k$-uniform hypergraph $H_k(n, p)$ (with $k \mid n$) to contain a perfect matching is $\Theta(n^{1-k}\log n)$ (Johansson-Kahn-Vu), and this follows in a few lines from the fractional expectation-threshold theorem by exhibiting a spread measure on perfect matchings. For a fixed strictly $1$-balanced graph $F$, the same argument applied to a spread measure on $F$-factors gives the upper bound $O(n^{-1/d_1(F)}\log n)$ for the $F$-factor threshold; the exact threshold $\Theta(n^{-1/d_1(F)}(\log n)^{1/e(F)})$ is the theorem of Johansson, Kahn and Vu.

## Proof sketch

The uniform measure on perfect matchings of the complete $k$-graph is $\kappa$-spread with $\kappa = \Theta(n^{k-1})$: a fixed set of $t$ disjoint edges lies in a random perfect matching with probability $\Theta(n^{-(k-1)})^{t}$. Spread measures certify $q_f \le O(1/\kappa)$, so the FKNP theorem gives $p_c = O(\log n/\kappa)$; the matching lower bound comes from isolated vertices.

## Depends on

- [Spread families and spread measures](../../extremal-set-theory/spread-families-and-robust-sunflowers/kappa-spread-families-and-measures.md)

## Proof depends on

- [Thresholds versus fractional expectation-thresholds](../thresholds-and-expectation-thresholds/theorem-1-1.md)
- [Kahn's theorem: the threshold in Shamir's problem is asymptotic to $n \log n$](../shamir-s-problem/matching-threshold-asymptotic-holds.md)

## Sources

- Keith Frankston, Jeff Kahn, Bhargav Narayanan, Jinyoung Park, "Thresholds versus fractional expectation-thresholds", Annals of Mathematics 194(2) (2021); arXiv:1910.13433.
- Anders Johansson, Jeff Kahn, Van Vu, "Factors in random graphs", Random Structures and Algorithms 33(1) (2008).
