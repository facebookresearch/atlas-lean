# AdaBoost training error is at most the exponential of the round errors

Run AdaBoost on $m > 0$ training points with labels $y$ and a weak learner that maps weights on the training points to predictions, and let $\varepsilon_t$ be the weighted error of the weak hypothesis of round $t$. If $\gamma \ge 0$ and $0 < \varepsilon_t \le 1/2 - \gamma$ for every round $t < T$, then the training error of the combined classifier after $T$ rounds is at most $\exp(-2\gamma^2 T)$. The edge condition is needed only for the $T$ rounds that are executed.
