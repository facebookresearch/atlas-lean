# Group privacy for pure differential privacy

Let $M$ be a mechanism on databases $\mathrm{Fin}\,n \to X$ with values in probability mass functions, [$\varepsilon$-differentially private](../differential-privacy/is-dp.md) for [replace-one adjacency](../differential-privacy/replace-one.md). If $d$ and $d'$ are joined by a [replace-one chain](replace-one-chain.md) of length $k$, then for every output $o$,

$$
M(d)(o) \le e^{k\varepsilon}\, M(d')(o).
$$

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Theorem 2.2.
