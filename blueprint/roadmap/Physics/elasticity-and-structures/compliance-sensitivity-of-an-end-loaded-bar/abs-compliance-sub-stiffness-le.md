# Stiffness step: compliance bound for stiffnesses at least kmin > 0

For $k_{\min} > 0$, stiffnesses $k \ge k_{\min}$ and $\hat k \ge k_{\min}$ and a force with
$|\hat F| \le F_{\max}$, the [compliance](compliance.md) $J(F, k) = F^2 / k$ satisfies

$$|J(\hat F, k) - J(\hat F, \hat k)| \le \frac{F_{\max}^2}{k_{\min}^2}\, |k - \hat k|,$$

by the difference of inverse stiffnesses
$\hat F^2 / k - \hat F^2 / \hat k = \hat F^2 (\hat k - k) / (k \hat k)$ with
$k \hat k \ge k_{\min}^2$.
