# Multicalibration implies omniprediction for convex Lipschitz losses

Let $\mathcal{C}$ be a class of bounded functions and $\mathcal{L}$ the convex losses $\ell(t,y)$ that are $1$-Lipschitz in $t$ on the relevant range. If $p$ is $\alpha$-multicalibrated with respect to (the level-set refinements of) $\mathcal{C}$, then $p$ is an $(\mathcal{L}, \mathcal{C}, O(\alpha))$-omnipredictor, up to an additive discretization error. Multicalibration thereby serves as a solution concept for agnostic boosting, and multigroup versions give omnipredictors for multi-group loss minimization.

## Proof sketch

Fix $\ell$ and $c \in \mathcal{C}$. On a level set $\{p = v\}$, multicalibration makes $c(x)$ nearly uncorrelated with $y - v$, so replacing $y$ by $\tilde y \sim \mathrm{Ber}(v)$ changes $\mathbb{E}[\ell(c(x), y)]$ by $O(\alpha)$ after a linearization that uses convexity and Lipschitzness. Under simulated outcomes, the optimal action given only $v$ is $k_\ell(v)$, which does at least as well as $c(x)$ by Jensen's inequality; undoing the simulation costs another $O(\alpha)$.

## Depends on

- [Omnipredictors](omnipredictor.md)
- [Multicalibrated predictors](../multicalibration-and-multiaccuracy/multicalibrated-predictor.md)

## Sources

- P. Gopalan, A. T. Kalai, O. Reingold, V. Sharan, U. Wieder, "Omnipredictors", ITCS (2022), arXiv:2109.05389.
