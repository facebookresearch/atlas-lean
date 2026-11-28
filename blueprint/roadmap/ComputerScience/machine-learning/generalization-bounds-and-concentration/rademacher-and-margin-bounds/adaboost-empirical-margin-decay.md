# Exponential decay of AdaBoost's empirical margin distribution

Run AdaBoost for $T$ rounds on a sample $((x_i, y_i))_{i \le m}$ with $y_i \in \{\pm 1\}$ and any deterministic weak learner, with weighted errors $\varepsilon_t$ and vote weights $w_t = \frac12\ln\frac{1-\varepsilon_t}{\varepsilon_t}$, and let $f = \sum_{t<T} w_t h_t / \sum_{t<T} w_t$ be the normalized score (if some round has $\varepsilon_t = 0$, $f$ is that round's hypothesis, and every point has margin $1$). If every $\varepsilon_t \le \frac12 - \gamma$ with $0 < \gamma < \frac12$, then for every $\rho \in [0, 2\gamma]$

$$
\frac{1}{m}\#\{i : y_i f(x_i) \le \rho\} \le \Big((1-2\gamma)^{1-\rho}(1+2\gamma)^{1+\rho}\Big)^{T/2},
$$

and if $\rho < \gamma$, then $(1-2\gamma)^{1-\rho}(1+2\gamma)^{1+\rho} < 1$, so the fraction of training margins at most $\rho$ decreases exponentially in $T$.

## Proof sketch

Start from the product bound $\prod_t 2\varepsilon_t^{(1-\rho)/2}(1-\varepsilon_t)^{(1+\rho)/2}$. Each factor is increasing in $\varepsilon_t$ on $(0, \frac{1-\rho}{2}]$, which contains $(0, \frac12 - \gamma]$ when $\rho \le 2\gamma$, so substitute $\varepsilon_t = \frac12 - \gamma$. The base equals $(1 - 4\gamma^2)\big(\frac{1+2\gamma}{1-2\gamma}\big)^{\rho}$, which is increasing in $\rho$, so for $\rho < \gamma$ it is below its value at $\rho = \gamma$, and that value is below $1$ by the computation below.

Explicit rate: for every $\rho \in [0, \gamma]$ the fraction is at most $e^{-2\gamma(\gamma-\rho)T}$, which at $\rho = 0$ is the training-error bound $e^{-2\gamma^2 T}$. Put $x = 2\gamma \in (0,1)$ and

$$
g(\rho) = \frac{1-\rho}{2}\ln(1-x) + \frac{1+\rho}{2}\ln(1+x),
$$

so that the bound above is $e^{T g(\rho)}$ and $-2\gamma(\gamma - \rho) = x\rho - x^2/2$. Both $g(\rho)$ and $x\rho - x^2/2$ are affine in $\rho$, so it suffices to compare them at $\rho = 0$ and $\rho = \gamma = x/2$. At $\rho = 0$, $g(0) = \frac12\ln(1-x^2) \le -\frac{x^2}{2}$ because $\ln(1-u) \le -u$. At $\rho = x/2$ the right side is $0$ and $g(x/2) = \frac12\big(\ln(1-x^2) + x\,\mathrm{artanh}\,x\big)$ with $\mathrm{artanh}\,x = \frac12\ln\frac{1+x}{1-x}$. For $|x| < 1$, $\ln(1-x^2) = -\sum_{k\ge1} x^{2k}/k$ and $x\,\mathrm{artanh}\,x = \sum_{k\ge1} x^{2k}/(2k-1)$, so

$$
\ln(1-x^2) + x\,\mathrm{artanh}\,x = \sum_{k\ge1}\Big(\frac{1}{2k-1} - \frac1k\Big)x^{2k} = -\sum_{k\ge2}\frac{k-1}{k(2k-1)}\,x^{2k} < 0.
$$

Hence $g(\rho) \le x\rho - x^2/2$ on $[0, x/2]$, and $g(x/2) < 0$ gives the strict inequality used above.

## Depends on

- [AdaBoost's training margins](../../online-learning-and-boosting/adaboost/margin-err-le.md)
- [The training margin error](../../online-learning-and-boosting/adaboost/margin-err.md)
- [The weak-learning assumption](../../online-learning-and-boosting/adaboost/weak-learner.md)

## Sources

- R. E. Schapire, Y. Freund, P. Bartlett and W. S. Lee, "Boosting the Margin: A New Explanation for the Effectiveness of Voting Methods", The Annals of Statistics, 1998.
- M. Mohri, A. Rostamizadeh and A. Talwalkar, "Foundations of Machine Learning", 2nd edition, MIT Press, 2018, Theorem 7.7 and (7.18).
