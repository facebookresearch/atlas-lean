# Group privacy for histograms

If $M$ is $\varepsilon$-differentially private for neighbouring histograms, then for all histograms
with $\|x - y\|_1 \le k$ and every measurable $S$, $M(x)(S) \le e^{k\varepsilon} M(y)(S)$. Two
histograms at $\ell_1$ distance at most $k$ are joined by a chain of at most $k$ single-record changes,
to which group privacy along a chain applies.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Theorem 2.2.
