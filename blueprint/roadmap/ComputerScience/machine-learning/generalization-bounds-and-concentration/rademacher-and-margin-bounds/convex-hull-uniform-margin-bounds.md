# Uniform-in-margin bounds for convex combinations of base classifiers

Let $\alpha$ be a measurable space, $D$ a probability distribution on $\alpha \times \{\pm 1\}$, and $H$ a class of measurable functions $\alpha \to \mathbb{R}$ (with the usual measurability of the suprema involved). For a margin $\rho > 0$ let $\Phi_\rho(u) = \min(1, \max(0, 1 - u/\rho))$ be the $\rho$-margin loss and $\hat{R}_{S,\rho}(h) = \frac{1}{m}\sum_i \Phi_\rho(y_i h(x_i))$ the empirical margin loss on $S = ((x_i, y_i))_{i \le m}$; $R_m(H)$ is the Rademacher complexity of $H$ under the marginal of $D$ on $\alpha$ and $\hat{R}_{S_X}(H)$ its empirical Rademacher complexity on the unlabelled points of $S$.
Let $r > 0$, $m > 0$ and $\delta > 0$. With probability at least $1-\delta$, simultaneously for every $f \in \mathrm{conv}(H)$ and $\rho \in (0, r]$, the uniform-in-margin bound holds with $R_m(H)$ of the base class, that is $\Pr_D[y f(x) \le 0] \le \hat{R}_{S,\rho}(f) + \frac{4}{\rho}R_m(H) + \sqrt{\ln\log_2(2r/\rho)/m} + \sqrt{\ln(2/\delta)/(2m)}$, and likewise its data-dependent form with $\hat{R}_{S_X}(H)$. If $H = \sigma(C)$ is the sign class of a binary class $C$ whose shattered sets have at most $d \le m$ points, then with probability at least $1 - \delta$, for every $f \in \mathrm{conv}(\sigma(C))$ and every $\rho \in (0, 1]$,

$$
\Pr_D[y\,f(x) \le 0] \le \hat{R}_{S,\rho}(f) + \frac{4}{\rho}\sqrt{\frac{2d\ln(em/d)}{m}} + \sqrt{\frac{\ln\log_2(2/\rho)}{m}} + \sqrt{\frac{\ln(2/\delta)}{2m}}.
$$

## Proof sketch

Apply the uniform-in-margin bound to $\mathrm{conv}(H)$ and convex-hull invariance. In the VC case, bound $R_m(\sigma(C))$ by Massart's lemma and Sauer's lemma, $\sqrt{2d\ln(em/d)/m}$, with $r = 1$.

## Depends on

- [Uniform-in-margin Rademacher generalization bound](uniform-in-margin-rademacher-bound.md)
- [Convex hull invariance](../rademacher-complexity/rademacher-complexity-convex-hull.md)
- [Rademacher complexity of a VC class, explicit rate](../rademacher-complexity/rademacher-complexity-sign-patterns-le-v.md)

## Sources

- M. Mohri, A. Rostamizadeh and A. Talwalkar, "Foundations of Machine Learning", 2nd edition, MIT Press, 2018, Theorem 5.9 and Corollaries 7.5 and 7.6.
- R. E. Schapire, Y. Freund, P. Bartlett and W. S. Lee, "Boosting the Margin: A New Explanation for the Effectiveness of Voting Methods", The Annals of Statistics, 1998.
