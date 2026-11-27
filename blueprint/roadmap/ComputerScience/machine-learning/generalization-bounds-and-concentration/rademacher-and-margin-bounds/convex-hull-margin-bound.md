# Fixed-margin generalization bound for convex combinations

Let $\alpha$ be a finite set, $D$ a probability distribution on $\alpha \times \{\pm 1\}$, and $H$ a uniformly bounded class of functions $\alpha \to \mathbb{R}$. For a margin $\rho > 0$ let $\Phi_\rho(u) = \min(1, \max(0, 1 - u/\rho))$ be the $\rho$-margin loss and $\hat{R}_{S,\rho}(h) = \frac{1}{m}\sum_i \Phi_\rho(y_i h(x_i))$ the empirical margin loss on $S = ((x_i, y_i))_{i \le m}$; $R_m(H)$ is the Rademacher complexity of $H$ under the marginal of $D$ on $\alpha$ and $\hat{R}_{S_X}(H)$ its empirical Rademacher complexity on the unlabelled points of $S$.
For $\rho > 0$, $m > 0$ and $\delta \in (0,1)$, with probability at least $1-\delta$ over $S \sim D^m$, every $f$ in the convex hull $\mathrm{conv}(H)$ (finite convex combinations $\sum_k \mu_k h_k$, $\mu_k \ge 0$, $\sum_k \mu_k = 1$) satisfies

$$
\Pr_D[y\,f(x) \le 0] \le \hat{R}_{S,\rho}(f) + \frac{2}{\rho}R_m(H) + \sqrt{\frac{\ln(1/\delta)}{2m}},
$$

a bound that does not depend on the number of combined hypotheses.

## Proof sketch

Apply the fixed-margin bound to the uniformly bounded class $\mathrm{conv}(H)$ and use convex-hull invariance of the Rademacher complexity, $R_m(\mathrm{conv}\,H) = R_m(H)$, which holds because the correlation with each fixed sign vector is affine in $f$.

## Depends on

- [Fixed-margin Rademacher generalization bound](fixed-margin-rademacher-bound.md)
- [Convex hull invariance](../rademacher-complexity/rademacher-complexity-convex-hull.md)
- [The complexity term of the margin bound for voting classifiers](../rademacher-complexity/rademacher-complexity-ramp-costs-convex.md)

## Proof depends on

- [Fixed-margin Rademacher generalization bound](fixed-margin-rademacher-bound.md)
- [Convex hull invariance](../rademacher-complexity/rademacher-complexity-convex-hull.md)

## Sources

- M. Mohri, A. Rostamizadeh and A. Talwalkar, "Foundations of Machine Learning", 2nd edition, MIT Press, 2018.
- R. E. Schapire, Y. Freund, P. Bartlett and W. S. Lee, "Boosting the Margin: A New Explanation for the Effectiveness of Voting Methods", The Annals of Statistics, 1998.
