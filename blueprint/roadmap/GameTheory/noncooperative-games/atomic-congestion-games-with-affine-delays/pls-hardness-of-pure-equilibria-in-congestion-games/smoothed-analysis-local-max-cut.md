# Local Max-Cut is efficient in smoothed analysis

Consider Local Max-Cut with the flip neighbourhood on an $n$-vertex graph whose edge weights are independent random variables with densities bounded by $\phi$ on $[-1, 1]$. Then, for every initial cut and every way of choosing the improving flips, the smoothed number of steps is bounded by a polynomial in $n^{\log n}$ and $\phi$ (quasi-polynomial smoothed complexity); and on complete graphs, for every $\eta > 0$, with high probability every implementation of the flip algorithm terminates within $O(\phi^5 n^{15 + \eta})$ steps. In contrast, in the worst case exponentially long improving sequences exist.

## Proof sketch

Each improving flip increases the cut weight by a linear combination of edge weights with coefficients in $\{-1, 0, 1\}$. Every sequence of $5n$ consecutive improving flips contains a subsequence in which the vertices that move do so repeatedly, in a $\Theta(\log n)$-repeating pattern, and for such a subsequence of length $\ell$ the rank of the corresponding linear combinations is at least about $\ell / (2k)$ for $k$-repeating patterns. Since independent weights with density at most $\phi$ make it unlikely that many linearly independent combinations are all tiny, a union bound over the $n^{O(\log n)}$ patterns shows that every block of $5n$ steps improves the bounded objective by a non-negligible amount, giving the quasi-polynomial bound. On complete graphs, a finer rank analysis shows that with high probability no improving sequence of length $2n$ has total improvement below $n^{-(12 + \eta)} \phi^{-5}$ (up to constants), which gives the polynomial bound.

## Depends on

- [MAX-CUT as an optimization problem](../../../../TheoryOfComputation/pcp-and-inapproximability/inapproximability-of-max-cut/max-cut.md)
- [Smoothed complexity](../../../../ComputerScience/sorting-and-searching/algorithm-analysis-models/smoothed-complexity.md)

## Proof depends on

- [Local Max-Cut under the flip neighbourhood is PLS-complete](local-max-cut-flip-pls-complete.md)

## Sources

- R. Etscheid, H. Röglin, "Smoothed Analysis of Local Search for the Maximum-Cut Problem", ACM Transactions on Algorithms 13(2) (2017); SODA 2014, Theorem 1.
- O. Angel, S. Bubeck, Y. Peres, F. Wei, "Local max-cut in smoothed polynomial time", STOC 2017, arXiv:1610.04807, Theorem 1.1 and Proposition 1.6.
