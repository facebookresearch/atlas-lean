# Force step: bound for force magnitudes at most Fmax and k ≥ kmin > 0

For $k_{\min} > 0$, a stiffness $k \ge k_{\min}$ and forces with $|F| \le F_{\max}$ and
$|\hat F| \le F_{\max}$, the [compliance](compliance.md) $J(F, k) = F^2 / k$ satisfies

$$|J(F, k) - J(\hat F, k)| \le \frac{2 F_{\max}}{k_{\min}}\, |F - \hat F|,$$

by the difference of squares $F^2 - \hat F^2 = (F - \hat F)(F + \hat F)$ with
$|F + \hat F| \le 2 F_{\max}$ and $k \ge k_{\min}$.
