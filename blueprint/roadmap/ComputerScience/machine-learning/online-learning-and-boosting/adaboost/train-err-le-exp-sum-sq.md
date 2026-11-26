# AdaBoost's training error in terms of the edges

AdaBoost runs on $m > 0$ training points with labels $y_i \in \{\pm 1\}$ and an arbitrary weak learner; $D_t$ are its weights, $h_t$ the weak hypothesis and $\varepsilon_t$ its weighted error in round $t$, $\alpha_t = \tfrac12 \log((1-\varepsilon_t)/\varepsilon_t)$, and $F_T = \sum_{t<T} \alpha_t h_t$ is the combined score. If every round $t < T$ has $0 < \varepsilon_t < 1$, then with the edges $\gamma_t = 1/2 - \varepsilon_t$,

$$\frac{1}{m} \#\{i : y_i F_T(x_i) \le 0\} \le \exp\Big(-2 \sum_{t < T} \gamma_t^2\Big).$$

Each round contributes its own edge, so rounds with larger edges make faster progress; with a uniform edge $\gamma_t \ge \gamma$ this is [the exponential bound $e^{-2 \gamma^2 T}$](train-err-le-exp.md). The training error is zero as soon as the right-hand side is below $1/m$.

## Sources

- Y. Freund and R. E. Schapire, "A decision-theoretic generalization of on-line learning and an application to boosting", *J. Comput. System Sci.* 55 (1997), 119–139, equation (21) (the bound of Theorem 6 rewritten in terms of $\gamma_t$).
