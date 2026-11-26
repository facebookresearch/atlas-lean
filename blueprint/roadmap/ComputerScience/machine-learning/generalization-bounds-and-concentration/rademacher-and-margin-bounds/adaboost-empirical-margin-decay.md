# Exponential decay of AdaBoost's empirical margin distribution

Run AdaBoost for $T$ rounds on a sample $((x_i, y_i))_{i \le m}$ with $y_i \in \{\pm 1\}$ and any deterministic weak learner, with weighted errors $\varepsilon_t$ and vote weights $w_t = \frac12\ln\frac{1-\varepsilon_t}{\varepsilon_t}$, and let $f = \sum_{t<T} w_t h_t / \sum_{t<T} w_t$ be the normalized score (if some round has $\varepsilon_t = 0$, $f$ is that round's hypothesis, and every point has margin $1$). If every $\varepsilon_t \le \frac12 - \gamma$ with $0 < \gamma < \frac12$, then for every $\rho \in [0, 2\gamma]$

$$
\frac{1}{m}\#\{i : y_i f(x_i) \le \rho\} \le \Big((1-2\gamma)^{1-\rho}(1+2\gamma)^{1+\rho}\Big)^{T/2},
$$

and for every $\rho \in [0, \gamma]$ this fraction is at most $e^{-2\gamma(\gamma-\rho)T}$, recovering the training-error bound $e^{-2\gamma^2 T}$ at $\rho = 0$.

## Proof sketch

Start from the product bound $\prod_t 2\varepsilon_t^{(1-\rho)/2}(1-\varepsilon_t)^{(1+\rho)/2}$. Each factor is increasing in $\varepsilon_t$ for $\rho \le 2\gamma$, so substitute $\varepsilon_t = \frac12 - \gamma$. Taking logarithms, $\frac{1-\rho}{2}\ln(1-2\gamma) + \frac{1+\rho}{2}\ln(1+2\gamma) \le -2\gamma(\gamma - \rho)$ for $0 \le \rho \le \gamma$ by concavity estimates of the logarithm.

## Depends on

- [AdaBoost's training margins](../../online-learning-and-boosting/adaboost/margin-err-le.md)
- [The training margin error](../../online-learning-and-boosting/adaboost/margin-err.md)
- [The weak-learning assumption](../../online-learning-and-boosting/adaboost/weak-learner.md)

## Proof depends on

- [AdaBoost's training margins](../../online-learning-and-boosting/adaboost/margin-err-le.md)

## Sources

- R. E. Schapire, Y. Freund, P. Bartlett and W. S. Lee, "Boosting the Margin: A New Explanation for the Effectiveness of Voting Methods", The Annals of Statistics, 1998.
- M. Mohri, A. Rostamizadeh and A. Talwalkar, "Foundations of Machine Learning", 2nd edition, MIT Press, 2018.
