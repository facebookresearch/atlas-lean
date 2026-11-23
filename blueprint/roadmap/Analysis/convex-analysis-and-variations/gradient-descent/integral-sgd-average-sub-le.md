# Convergence of stochastic gradient descent

Let $f$ be convex on a finite-dimensional real inner product space $E$. Let $\xi_0, \xi_1, \dots$ be i.i.d. random variables with law $\nu$ and let $G : E \times \Xi \to E$ be jointly measurable with $\|G(\theta, \xi)\| \le B$ and with mean $\int G(\theta, \xi) \, d\nu(\xi)$ a subgradient of $f$ at every $\theta$. Run stochastic gradient descent

$$
\theta_{t+1} = \theta_t - \gamma_t \, G(\theta_t, \xi_t), \qquad \gamma_t = \frac{D}{B \sqrt{t + 1}},
$$

from a deterministic $\theta_0$. Then for every point $\theta^\star$ with $\|\theta_0 - \theta^\star\| \le D$, in particular a minimizer, and every $t \ge 1$, the weighted average $\bar\theta_t = \sum_{s \lt t} \gamma_s \theta_s / \sum_{s \lt t} \gamma_s$ satisfies

$$
\mathbb{E}\big[f(\bar\theta_t)\big] - f(\theta^\star) \le \frac{D B (2 + \log t)}{2 \sqrt{t}}.
$$

The proof is that of the subgradient method with expectations: $\theta_t$ is a measurable function of $\xi_0, \dots, \xi_{t-1}$, hence independent of $\xi_t$, and Fubini's theorem gives $\mathbb{E}\langle G(\theta_t, \xi_t), \theta_t - \theta^\star \rangle \ge \mathbb{E}[f(\theta_t)] - f(\theta^\star)$, and Jensen's inequality passes to the average iterate.

With $f$ the expected risk and $G(\theta, \xi)$ the gradient of the loss at one fresh example $\xi$, this is single-pass stochastic gradient descent on the expected risk itself: after $n$ examples its excess risk is of order $D B / \sqrt{n}$, the same rate as the estimation error of empirical risk minimization over the ball of radius $D$, at the cost of $n$ gradient evaluations.

## Background

- [Convergence of the subgradient method](subgradient-method-rate.md): background, the deterministic version.
- [Rademacher average of a ball of linear predictors](../../../ComputerScience/machine-learning/generalization-bounds-and-concentration/rademacher-average-linear-ball-le.md): background, the matching $D R / \sqrt{n}$ complexity of the ball, which governs the estimation error of empirical risk minimization.

## Sources

- F. Bach, *Learning Theory from First Principles*, MIT Press (2024); author PDF at <https://www.di.ens.fr/~fbach/ltfp_book.pdf>, Section 5.4, Proposition 5.7, under assumptions (H-1) (unbiased gradient) and (H-2) (bounded gradient); the stochastic gradients are modelled by independent gradient functions, as the source suggests after (H-2). The source indexes steps from $1$, with $\gamma_t = (D/B)/\sqrt{t}$ multiplying the gradient at $\theta_{t-1}$, and takes $\theta^\star$ a minimizer of a $B$-Lipschitz $f$; here Lipschitz continuity follows from the bound on the subgradients, and any comparison point at distance at most $D$ is allowed.
