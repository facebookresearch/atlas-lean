# Uniform-in-margin Rademacher generalization bound

Let $\alpha$ be a measurable space, $D$ a probability distribution on $\alpha \times \{\pm 1\}$, and $H$ a class of measurable functions $\alpha \to \mathbb{R}$ (with the usual measurability of the suprema involved). For a margin $\rho > 0$ let $\Phi_\rho(u) = \min(1, \max(0, 1 - u/\rho))$ be the $\rho$-margin loss and $\hat{R}_{S,\rho}(h) = \frac{1}{m}\sum_i \Phi_\rho(y_i h(x_i))$ the empirical margin loss on $S = ((x_i, y_i))_{i \le m}$; $R_m(H)$ is the Rademacher complexity of $H$ under the marginal of $D$ on $\alpha$ and $\hat{R}_{S_X}(H)$ its empirical Rademacher complexity on the unlabelled points of $S$.
Let $r > 0$, $m > 0$ and $\delta > 0$. With probability at least $1 - \delta$ over $S \sim D^m$, simultaneously for every $h \in H$ and every margin $\rho \in (0, r]$,

$$
\Pr_D[y\,h(x) \le 0] \le \hat{R}_{S,\rho}(h) + \frac{4}{\rho}R_m(H) + \sqrt{\frac{\ln\log_2(2r/\rho)}{m}} + \sqrt{\frac{\ln(2/\delta)}{2m}},
$$

and, with probability at least $1-\delta$, simultaneously the data-dependent bound

$$
\Pr_D[y\,h(x) \le 0] \le \hat{R}_{S,\rho}(h) + \frac{4}{\rho}\hat{R}_{S_X}(H) + 3\sqrt{\frac{\ln\log_2(2r/\rho)}{m}} + 3\sqrt{\frac{\ln(4/\delta)}{2m}}.
$$

## Proof sketch

Apply the fixed-margin bound at the dyadic margins $\rho_n = r/2^{n+1}$ with confidence $\delta_n = \delta/((n+1)(n+2))$, whose sum is $\delta$, and take a union bound. For $\rho \in (r/2^{n+1}, r/2^n]$, monotonicity of $\Phi$ in the margin gives $\Phi_{\rho_n} \le \Phi_\rho$, $2/\rho_n \le 4/\rho$, and $(n+1)(n+2) \le 2\log_2(2r/\rho)^2$; split the square root with $\sqrt{a+b} \le \sqrt{a} + \sqrt{b}$.

## Depends on

- [Fixed-margin Rademacher generalization bound](fixed-margin-rademacher-bound.md)

## Sources

- M. Mohri, A. Rostamizadeh and A. Talwalkar, "Foundations of Machine Learning", 2nd edition, MIT Press, 2018, Theorem 5.9.
- V. Koltchinskii and D. Panchenko, "Empirical Margin Distributions and Bounding the Generalization Error of Combined Classifiers", The Annals of Statistics, 2002.
