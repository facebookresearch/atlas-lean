# Freund and Schapire's training-error bound with per-round errors

AdaBoost runs on $m > 0$ training points with labels $y_i \in \{\pm 1\}$ and an arbitrary weak learner; $D_t$ are its weights, $h_t$ the weak hypothesis and $\varepsilon_t$ its weighted error in round $t$, $\alpha_t = \tfrac12 \log((1-\varepsilon_t)/\varepsilon_t)$, and $F_T = \sum_{t<T} \alpha_t h_t$ is the combined score. If every round $t < T$ has $0 < \varepsilon_t < 1$, then the training error of $\operatorname{sign} F_T$ (a zero score counting as an error) satisfies

$$\frac{1}{m} \#\{i : y_i F_T(x_i) \le 0\} \le \prod_{t < T} 2 \sqrt{\varepsilon_t (1 - \varepsilon_t)}.$$

No edge is assumed: rounds with $\varepsilon_t \ge 1/2$ are allowed, as Freund and Schapire note before their Theorem 6. The excluded case $\varepsilon_t = 0$ is a perfect weak hypothesis, for which $\alpha_t$ is infinite. The [uniform-edge version](train-err-le-prod-sqrt.md) is the special case in which a weak learner with edge $\gamma$ guarantees $0 < \varepsilon_t \le 1/2 - \gamma$ in every round.

## Informally uses

- [The Hedge loss bound](../hedge-algorithm/alg-loss-le.md): Freund and Schapire's proof adapts the weight-decay argument of their Lemma 1 and Theorem 2 (the Hedge bound), with the step size now chosen per round.

## Sources

- Y. Freund and R. E. Schapire, "A decision-theoretic generalization of on-line learning and an application to boosting", *J. Comput. System Sci.* 55 (1997), 119–139, Theorem 6, equation (14), and the remark preceding it (journal version).
