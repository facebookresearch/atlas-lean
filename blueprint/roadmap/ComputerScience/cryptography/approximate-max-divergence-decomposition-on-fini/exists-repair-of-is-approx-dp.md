# Repairing the output distribution of a private mechanism

Let $M$ be a mechanism with values in probability mass functions on a finite nonempty type, [$(\varepsilon, \delta)$-differentially private](../approximate-differential-privacy/is-approx-dp.md) for $\mathrm{adj}$. For every pair with $\mathrm{adj}(d, d')$ there is a probability mass function $\tilde P$ with total variation distance at most $\delta$ from $M(d)$ and [pure max-divergence](max-div-le.md) $D_\infty(\tilde P \| M(d')) \le \varepsilon$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Lemma 3.17, part 1.
