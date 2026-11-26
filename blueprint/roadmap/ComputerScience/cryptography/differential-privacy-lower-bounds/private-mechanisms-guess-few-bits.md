# A differentially private mechanism guesses few secret bits

Let $G$ map databases $d \in \{0,1\}^n$ to guesses in $\{0,1\}^n$ and be $(\varepsilon, \delta)$-differentially private for Hamming adjacency. Then, for a uniformly random database $d$, the expected number of coordinates on which $G(d)$ agrees with $d$ is at most

$$
\frac{e^\varepsilon}{1 + e^\varepsilon}\, n + \frac{\delta}{1 + e^\varepsilon}\, n .
$$

Consequently, for $\varepsilon$ small and $\delta = o(1)$, any private mechanism errs on almost half of the rows in expectation, so a mechanism whose answers allow reconstruction of all but $o(n)$ bits cannot be differentially private.

## Proof sketch

For each coordinate $i$, pair each database with its neighbour obtained by flipping bit $i$; privacy bounds the probability of guessing bit $i$ correctly on one by $e^\varepsilon$ times the probability of guessing it incorrectly on the other plus $\delta$; summing over the pairs and coordinates gives the bound.

## Depends on

- [Differential privacy](../differential-privacy/differentially-private.md)
- [Neighbouring row databases](../differential-privacy/hamming-adj.md)

## Sources

- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science, 2014.
