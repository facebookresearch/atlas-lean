# Approximate differential privacy is preserved by randomized post-processing

If $M$ is [$(\varepsilon, \delta)$-differentially private](is-approx-dp.md) for $\mathrm{adj}$ and $k$ assigns to each output $a$ a probability mass function $k(a)$ on a second output type, then the mechanism $d \mapsto \sum_a M(d)(a)\, k(a)$ (first run $M$, then sample from $k$ at its output) is $(\varepsilon, \delta)$-differentially private for $\mathrm{adj}$. The kernel $k$ does not depend on the database.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Proposition 2.1.
