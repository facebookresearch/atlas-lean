# Margin generalization bounds for AdaBoost independent of the number of rounds

Let $\alpha$ be a measurable space, $D$ a distribution on $\alpha \times \{\pm 1\}$, and $C$ a class of measurable binary base classifiers whose shattered sets have at most $d \le m$ points (with the usual measurability of the suprema involved). With probability at least $1-\delta$ over $S \sim D^m$, for every deterministic weak learner whose first $T > 0$ rounds return hypotheses in $C$ with weighted errors below $\frac12$, and every $\rho \in (0, 1]$, the AdaBoost classifier $F_T$ with normalized score $f \in \mathrm{conv}(\sigma(C))$ satisfies

$$
\Pr_D[F_T(x) \ne y] \le \hat{R}_{S,\rho}(f) + \frac{4}{\rho}\sqrt{\frac{2d\ln(em/d)}{m}} + \sqrt{\frac{\ln\log_2(2/\rho)}{m}} + \sqrt{\frac{\ln(2/\delta)}{2m}}.
$$

If moreover every round has error at most $\frac12 - \gamma$ with $0 < \gamma < \frac12$, then with probability at least $1-\delta$, for every such weak learner, every $T > 0$ and every $\rho \in (0, 2\gamma]$,

$$
\Pr_D[F_T(x) \ne y] \le \Big((1-2\gamma)^{1-\rho}(1+2\gamma)^{1+\rho}\Big)^{T/2} + \frac{4}{\rho}\sqrt{\frac{2d\ln(em/d)}{m}} + \sqrt{\frac{\ln\log_2(2/\rho)}{m}} + \sqrt{\frac{\ln(2/\delta)}{2m}},
$$

where the first term decreases exponentially in $T$ when $\rho < \gamma$.

## Proof sketch

When every round has error below $\frac12$, all vote weights are positive and the normalized score lies in $\mathrm{conv}(\sigma(C))$; a sign error of $F_T$ means a nonpositive margin of $f$. Apply the uniform VC margin bound for convex combinations, which holds for all $f$ at once and hence for every weak learner and every $T$. Under the edge assumption, bound $\hat{R}_{S,\rho}(f)$ by the fraction of margins at most $\rho$ and use the exponential margin decay; for $\rho \in (0, \gamma]$ its explicit rate bounds the first term by $e^{-2\gamma(\gamma-\rho)T}$.

## Depends on

- [Uniform-in-margin bounds for convex combinations of base classifiers](convex-hull-uniform-margin-bounds.md)
- [Exponential decay of AdaBoost's empirical margin distribution](adaboost-empirical-margin-decay.md)
- [AdaBoost's combined score](../../online-learning-and-boosting/adaboost/score.md)

## Sources

- R. E. Schapire, Y. Freund, P. Bartlett and W. S. Lee, "Boosting the Margin: A New Explanation for the Effectiveness of Voting Methods", The Annals of Statistics, 1998.
- M. Mohri, A. Rostamizadeh and A. Talwalkar, "Foundations of Machine Learning", 2nd edition, MIT Press, 2018, Theorem 5.9, Corollaries 7.5 and 7.6, Theorem 7.7.
- Y. Freund and R. E. Schapire, "A Decision-Theoretic Generalization of On-Line Learning and an Application to Boosting", Journal of Computer and System Sciences, 1997.
