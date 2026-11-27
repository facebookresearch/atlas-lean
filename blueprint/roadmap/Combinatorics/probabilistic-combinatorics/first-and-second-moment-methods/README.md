# First and second moment methods

The first moment method shows that a nonnegative integer count $X$ is $0$ with high probability when $\mathbb E X \to 0$; the second moment method shows that $X > 0$ with high probability when $\operatorname{Var} X = o((\mathbb E X)^2)$. For a count $X = \sum_i 1_{A_i}$ of events with a dependency graph, $\operatorname{Var} X \le \mu + \Delta$, which reduces thresholds for subgraph containment in $G(n,p)$ to estimating the correlation sum $\Delta$.

- [First moment method](measure-real-one-le-le-integral.md)
- [Second moment method](measure-real-eq-zero-le-variance-div-sq.md)
- [Second moment method, Cauchy–Schwarz form](sq-integral-le-integral-sq-mul-measure-r.md)
- [Number of events that occur](count.md)
- [Expected number of events](expected-count.md)
- [Correlation sum over dependent pairs](dependent-pair-sum.md)
- [Variance of a count of events with a dependency graph](variance-sum-indicator-le.md)
- [Second moment method for counts of events](measure-real-forall-not-mem-le.md)

## Related topics

- [Janson's inequalities](../janson-s-inequalities/README.md): the exponential counterpart of the second moment method for the same counts of contained sets.
- [Moment bounds for counting](../moment-bounds-for-counting/README.md): Chebyshev-type bounds on finite counts from their first two moments.
- [Thresholds and expectation thresholds](../thresholds-and-expectation-thresholds/README.md): the first moment method gives the expectation threshold as a lower bound for the threshold.
- [Concentration inequalities](../../../Probability/concentration-inequalities/README.md): Chebyshev, Paley–Zygmund and the exponential tail bounds behind these methods.
- [Graph colouring](../../../GraphTheory/graph-coloring/README.md): Erdős's graphs of high girth and high chromatic number come from the first moment method with alterations.
