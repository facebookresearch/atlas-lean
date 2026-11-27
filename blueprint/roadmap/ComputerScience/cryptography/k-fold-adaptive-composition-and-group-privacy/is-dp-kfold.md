# Adaptive k-fold composition of pure differential privacy

If $\varepsilon_i \ge 0$ for $i < k$ and, for every $i < k$ and every transcript $t$ after $i$ steps, the step mechanism $d \mapsto K_i(t, d)$ is [$\varepsilon_i$-differentially private](../differential-privacy/is-dp.md) for $\mathrm{adj}$, then the [$k$-fold adaptive composition](kfold-compose.md) is $\big(\sum_{i<k} \varepsilon_i\big)$-differentially private for $\mathrm{adj}$.
