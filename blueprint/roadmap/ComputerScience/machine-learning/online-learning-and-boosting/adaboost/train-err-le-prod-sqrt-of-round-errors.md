# Train Err le prod sqrt of round errors

Run AdaBoost on $m > 0$ training points with labels $y$ and a weak learner that maps weights on the training points to predictions, and let $\varepsilon_t$ be the weighted error of the weak hypothesis of round $t$. If $0 < \varepsilon_t < 1$ for every round $t < T$, then the training error of the combined classifier after $T$ rounds is at most $\prod_{t < T} 2\sqrt{\varepsilon_t (1 - \varepsilon_t)}$. The condition on the errors is needed only for the $T$ rounds that are executed.
