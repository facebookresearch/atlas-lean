# Compliance error bound: parameter steps plus four supplied error terms

Let $k_{\min} > 0$, let $|F| \le F_{\max}$, $|\hat F| \le F_{\max}$, $k \ge k_{\min}$ and
$\hat k \ge k_{\min}$, and let $J_{\mathrm{model}}$, $J_{\mathrm{disc}}$, $J_{\mathrm{solve}}$ and
$J_{\mathrm{comp}}$ be real numbers with the supplied bounds

$$
|J(\hat F, \hat k) - J_{\mathrm{model}}| \le e_{\mathrm{model}}, \quad
|J_{\mathrm{model}} - J_{\mathrm{disc}}| \le e_{\mathrm{disc}}, \quad
|J_{\mathrm{disc}} - J_{\mathrm{solve}}| \le e_{\mathrm{solve}}, \quad
|J_{\mathrm{solve}} - J_{\mathrm{comp}}| \le e_{\mathrm{arith}}.
$$

Then the [compliance](compliance.md) $J(F, k) = F^2 / k$ at the parameters $(F, k)$ satisfies

$$
|J(F, k) - J_{\mathrm{comp}}| \le \frac{2 F_{\max}}{k_{\min}}\, |F - \hat F| +
\frac{F_{\max}^2}{k_{\min}^2}\, |k - \hat k| +
e_{\mathrm{model}} + e_{\mathrm{disc}} + e_{\mathrm{solve}} + e_{\mathrm{arith}}.
$$

In the intended reading $(\hat F, \hat k)$ are the estimated inputs, $J_{\mathrm{model}}$ is the
compliance of the analysis model, $J_{\mathrm{disc}}$ its discretization, $J_{\mathrm{solve}}$ the
output of the algebraic solver and $J_{\mathrm{comp}}$ the computed value, and each supplied bound
carries its own provenance; the inequality holds for any real numbers satisfying the four bounds.
