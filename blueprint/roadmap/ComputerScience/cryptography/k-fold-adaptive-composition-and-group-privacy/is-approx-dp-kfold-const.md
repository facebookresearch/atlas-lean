# Non-adaptive k-fold composition of approximate differential privacy

Let $M_i$ be mechanisms with values in probability mass functions on $A_i$, and suppose that for every $i < k$, $\varepsilon_i \ge 0$, $\delta_i \ge 0$ and $M_i$ is [$(\varepsilon_i, \delta_i)$-differentially private](../approximate-differential-privacy/is-approx-dp.md) for $\mathrm{adj}$. Then the [$k$-fold composition](kfold-compose.md) whose $i$-th step ignores the earlier transcript and runs $M_i$ is $\big(\sum_{i<k} \varepsilon_i, \sum_{i<k} \delta_i\big)$-differentially private for $\mathrm{adj}$.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Theorem 3.16.
