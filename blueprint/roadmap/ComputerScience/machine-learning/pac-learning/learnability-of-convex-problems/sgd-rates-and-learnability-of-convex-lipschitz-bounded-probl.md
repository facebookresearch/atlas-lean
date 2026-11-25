# SGD rates and learnability of convex-Lipschitz-bounded problems

This node collects stochastic gradient descent guarantees for convex-Lipschitz-bounded learning problems.

## Expansion

A sound expansion has separate pages for:

1. **Unprojected SGD** (Shalev-Shwartz and Ben-David, Theorem 14.8): started at $0$ with step size
   $\eta = B/(\rho\sqrt T)$ and unbiased subgradient estimates of norm at most $\rho$, the averaged iterate has expected
   excess risk at most $B\rho/\sqrt T$ against every $w^*$ with $\lVert w^* \rVert \le B$. The average need not lie in
   the hypothesis class.
2. **Projected SGD,** a derivation from the source's projection step: for a nonempty, closed, convex $H$ inside the
   ball of radius $B$, starting at the projection of $0$ onto $H$ and projecting every update onto $H$, the averaged
   iterate lies in $H$ and has expected excess risk at most $B\rho/\sqrt T$ against $\inf_H L_D$.
3. **Sample complexity.** $T = m \ge B^2\rho^2/\varepsilon^2$ gives expected excess at most $\varepsilon$, and by
   Markov's inequality on the nonnegative excess of the projected learner, $m \ge B^2\rho^2/(\varepsilon^2\delta^2)$
   gives excess at most $\varepsilon$ with probability at least $1 - \delta$; from an arbitrary feasible start the
   distance bound is $2B$ and the thresholds are four times larger.
4. Strongly convex rates and confidence boosting, as separate pages.

## Depends on

- [Convex-Lipschitz-bounded and convex-smooth-bounded learning problems](convex-lipschitz-bounded-and-convex-smooth-bounded-learning.md)

## Related topics

- [Convergence of stochastic gradient descent](../../../../Analysis/convex-analysis-and-variations/gradient-descent/integral-sgd-average-sub-le.md)

## Sources

- Understanding Machine Learning: From Theory to Algorithms — Shalev-Shwartz, Ben-David / Cambridge University Press, Theorem 14.8, Sec 14.5, Theorem 14.11. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
