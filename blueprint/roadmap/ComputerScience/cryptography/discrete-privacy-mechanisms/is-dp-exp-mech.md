# The exponential mechanism is differentially private

Let $R$ be finite and nonempty, $\varepsilon \ge 0$ and $\Delta > 0$. If $|u(d, r) - u(d', r)| \le \Delta$ for every output $r$ whenever $\mathrm{adj}(d, d')$, then the [exponential mechanism](exp-mech.md) with parameters $\varepsilon$, $\Delta$ is [$\varepsilon$-differentially private](../differential-privacy/is-dp.md) for $\mathrm{adj}$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Theorem 3.10.
