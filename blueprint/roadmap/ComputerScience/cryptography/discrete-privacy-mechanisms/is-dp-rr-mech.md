# Randomized response is differentially private

If $\tfrac12 < p < 1$, then [randomized response](rr-mech.md) with parameter $p$ is [$\varepsilon$-differentially private](../differential-privacy/is-dp.md) for [bit adjacency](rr-adj.md), with

$$
\varepsilon = \log \frac{p}{1 - p} .
$$

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Section 3.2.
