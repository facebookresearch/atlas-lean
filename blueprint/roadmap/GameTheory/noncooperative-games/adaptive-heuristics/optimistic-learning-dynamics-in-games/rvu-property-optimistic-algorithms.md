# Regret bounded by variation in utilities for optimistic algorithms

An online learning algorithm on the simplex satisfies the RVU property with parameters $\alpha > 0$ and $0 < \beta \le \gamma$ if against every loss sequence

$$
\mathrm{Reg}_T \le \alpha + \beta \sum_{t = 1}^T \lVert \ell^t - \ell^{t-1} \rVert_\infty^2 - \gamma \sum_{t = 1}^T \lVert x^t - x^{t-1} \rVert_1^2 .
$$

Optimistic Hedge with step size $\eta$ satisfies RVU with $\alpha = (\log n)/\eta$, $\beta = \eta$ and $\gamma = 1/(4\eta)$; more generally, optimistic follow-the-regularized-leader with step size $\eta$ and a regularizer $R$ that is $1$-strongly convex with respect to a norm $\lVert\cdot\rVert$ satisfies RVU with $\alpha = (\max R - \min R)/\eta$, $\beta = \eta$ and $\gamma = 1/(4\eta)$, where the loss differences are measured in the dual norm $\lVert\cdot\rVert_*$ and the iterate differences in $\lVert\cdot\rVert$.

## Proof sketch

Analyse optimistic FTRL as FTRL with an extra predicted loss: the standard be-the-leader argument gives regret at most the regularizer range over $\eta$ plus the sum of inner products of the prediction errors with the consecutive iterate differences, minus the strong-convexity terms. Bounding the inner products by Hölder and Young's inequalities converts them to $\eta \lVert \ell^t - \ell^{t-1}\rVert_\infty^2$ plus a fraction of $\lVert x^{t} - x^{t-1}\rVert_1^2 / \eta$, leaving a negative stability term.

## Depends on

- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)

## Proof depends on

- [The Hedge loss bound](../../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/alg-loss-le.md)

## Sources

- V. Syrgkanis, A. Agarwal, H. Luo, R. E. Schapire, "Fast Convergence of Regularized Learning in Games", NeurIPS 2015, arXiv:1507.00407.
- A. Rakhlin, K. Sridharan, "Optimization, Learning, and Games with Predictable Sequences", NeurIPS 2013, arXiv:1311.1869.
