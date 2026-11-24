# Compliance error between two admissible parameter points

Call a force $F$ and a stiffness $k$ admissible when $|F| \le F_{\max}$ and $k \ge k_{\min}$, with
$k_{\min} > 0$. For admissible $(F, k)$ and $(\hat F, \hat k)$, the [compliance](compliance.md)
$J(F, k) = F^2 / k$ satisfies

$$
|J(F, k) - J(\hat F, \hat k)| \le \frac{2 F_{\max}}{k_{\min}}\, |F - \hat F| +
\frac{F_{\max}^2}{k_{\min}^2}\, |k - \hat k|,
$$

obtained through the intermediate value $J(\hat F, k)$: the
[force step](abs-compliance-sub-force-le.md) and the
[stiffness step](abs-compliance-sub-stiffness-le.md) are added by the triangle inequality. The bound
is deterministic.
