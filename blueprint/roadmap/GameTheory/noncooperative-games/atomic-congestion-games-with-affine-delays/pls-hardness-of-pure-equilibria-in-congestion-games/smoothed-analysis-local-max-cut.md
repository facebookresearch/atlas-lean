# Local Max-Cut is efficient in smoothed analysis

Consider Local Max-Cut with the flip neighbourhood on an $n$-vertex graph whose edge weights are independent random variables with densities bounded by $\phi$ on $[-1, 1]$. Then, from any initial cut, every sequence of improving flips has length at most $\phi\, n^{O(\log n)}$ with high probability (quasi-polynomial smoothed complexity), and on complete graphs a specific randomized improving-flip rule reaches a local optimum in polynomially many steps with high probability. In contrast, in the worst case exponentially long improving sequences exist.

## Proof sketch

Show that long improving sequences must contain short subsequences, of length $O(\log n)$, in which few distinct vertices flip; the total improvement of such a block is a nonzero integer combination of few random edge weights, which is unlikely to be tiny. A union bound over all possible block patterns, whose number is $n^{O(\log n)}$, bounds the probability that every block improves by less than $\varepsilon$, and since the objective is bounded, the number of improving steps is quasi-polynomial. On complete graphs a rank argument over many disjoint blocks improves the bound to polynomial.

## Depends on

- [MAX-CUT as an optimization problem](../../../../TheoryOfComputation/pcp-and-inapproximability/inapproximability-of-max-cut/max-cut.md)
- [Smoothed complexity](../../../../ComputerScience/sorting-and-searching/algorithm-analysis-models/smoothed-complexity.md)

## Proof depends on

- [Local Max-Cut under the flip neighbourhood is PLS-complete](local-max-cut-flip-pls-complete.md)

## Sources

- R. Etscheid, H. Röglin, "Smoothed Analysis of Local Search for the Maximum-Cut Problem", ACM Transactions on Algorithms 13(2) (2017); SODA 2014.
- O. Angel, S. Bubeck, Y. Peres, F. Wei, "Local max-cut in smoothed polynomial time", STOC 2017, arXiv:1610.04807.
