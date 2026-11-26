# Approximate max-divergence yields a nearby pure bound

Let $\Omega$ be a finite nonempty type and $P, Q$ probability mass functions on $\Omega$, and $\varepsilon \ge 0$, $\delta \ge 0$. If the [approximate max-divergence bound](approx-max-div-le.md) $D_\infty^\delta(P \| Q) \le \varepsilon$ holds, then there is a probability mass function $\tilde P$ on $\Omega$ with total variation distance $\mathrm{TV}(P, \tilde P) = \tfrac12 \sum_{w} |P(w) - \tilde P(w)|$ at most $\delta$ and [pure max-divergence](max-div-le.md) $D_\infty(\tilde P \| Q) \le \varepsilon$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Lemma 3.17, part 1.
