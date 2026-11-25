# Empirical area under the ROC curve

Let $x_1, \dots, x_m$ be positive scores and $y_1, \dots, y_n$ negative scores. The trapezoidal area under the empirical ROC curve is

$$\mathrm{AUC}(x, y) = \sum_{t} \frac{\big(\mathrm{TPR}_y(t) - \mathrm{TPR}^{>}_y(t)\big)\big(\mathrm{TPR}_x(t) + \mathrm{TPR}^{>}_x(t)\big)}{2},$$

the sum running over the distinct observed scores $t \in \{x_i\} \cup \{y_j\}$: the trapezoid from the point $(\mathrm{TPR}^{>}_y(t), \mathrm{TPR}^{>}_x(t))$ to $(\mathrm{TPR}_y(t), \mathrm{TPR}_x(t))$, with the [rates](roc-rate.md) at or above and [strictly above](roc-rate-above.md) $t$.
