# Adaptive k-fold composition of approximate differential privacy

Let $\varepsilon_i, \delta_i$ be real numbers with $\varepsilon_i \ge 0$ and $\delta_i \ge 0$ for $i < k$, and suppose that for every $i < k$ and every transcript $t$ after $i$ steps, the step mechanism $d \mapsto K_i(t, d)$ is [$(\varepsilon_i, \delta_i)$-differentially private](../approximate-differential-privacy/is-approx-dp.md) for the relation $\mathrm{adj}$. Then the [$k$-fold adaptive composition](kfold-compose.md) is differentially private for $\mathrm{adj}$ with budgets

$$
\Big(\sum_{i < k} \varepsilon_i,\ \sum_{i < k} \delta_i\Big).
$$

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Theorem 3.16 (stated there for non-adaptive composition).
