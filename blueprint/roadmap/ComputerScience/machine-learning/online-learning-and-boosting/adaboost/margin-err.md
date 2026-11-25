# The training margin error

AdaBoost runs on $m > 0$ training points with labels $y_i \in \{\pm 1\}$ and an arbitrary weak learner; $D_t$ are its weights, $h_t$ the weak hypothesis and $\varepsilon_t$ its weighted error in round $t$, $\alpha_t = \tfrac12 \log((1-\varepsilon_t)/\varepsilon_t)$, and $F_T = \sum_{t<T} \alpha_t h_t$ is the combined score. For a threshold $\theta \in \mathbb{R}$, the training margin error after $T$ rounds is the fraction of training points whose normalized margin $y_i F_T(x_i) / \sum_{t<T} \alpha_t$ is at most $\theta$, written without division as

$$\frac{1}{m} \#\Big\{i : y_i F_T(x_i) \le \theta \sum_{t<T} \alpha_t\Big\}.$$

For $\theta = 0$ it is the training error. The normalized vote $f = F_T / \sum_t \alpha_t$ lies in the convex hull of the weak hypotheses, and $y f(x) \in [-1, 1]$ is the margin of Schapire, Freund, Bartlett and Lee.

## Sources

- R. E. Schapire, Y. Freund, P. Bartlett and W. S. Lee, "Boosting the margin: a new explanation for the effectiveness of voting methods", *Ann. Statist.* 26 (1998), 1651–1686, Section 2 (margins) and equation (10).
