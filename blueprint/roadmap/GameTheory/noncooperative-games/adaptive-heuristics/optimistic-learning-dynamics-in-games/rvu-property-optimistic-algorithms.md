# Regret bounded by variation in utilities for optimistic algorithms

A vanishing-regret online learning algorithm on the simplex, one whose regret is $o(T)$ against every loss sequence, satisfies the RVU property with parameters $\alpha > 0$ and $0 < \beta \le \gamma$ if against every loss sequence

$$
\mathrm{Reg}_T \le \alpha + \beta \sum_{t = 1}^T \lVert \ell^t - \ell^{t-1} \rVert_\infty^2 - \gamma \sum_{t = 1}^T \lVert x^t - x^{t-1} \rVert_1^2 .
$$

Optimistic follow-the-regularized-leader with step size $\eta$, a regularizer $R$ that is $1$-strongly convex with respect to a norm $\lVert\cdot\rVert$, and the previous loss $\ell^{t-1}$ as its prediction of $\ell^t$ (so that $x^t$ minimizes $\langle x, \sum_{s < t} \ell^s + \ell^{t-1} \rangle + R(x)/\eta$) satisfies the bound above, with $\lVert\cdot\rVert_\infty$ replaced by the dual norm $\lVert\cdot\rVert_*$ for the loss differences and $\lVert\cdot\rVert_1$ by $\lVert\cdot\rVert$ for the iterate differences, with $\alpha = (\max R - \min R)/\eta$, $\beta = \eta$ and $\gamma = 1/(4\eta)$. Optimistic Hedge is the case of the entropy regularizer, which is $1$-strongly convex with respect to $\lVert\cdot\rVert_1$, with $\alpha = (\log n)/\eta$, $\beta = \eta$ and $\gamma = 1/(4\eta)$. The condition $\beta \le \gamma$ of the definition, $\eta \le 1/(4\eta)$, holds exactly when $\eta \le 1/2$, so these algorithms have the RVU property for step sizes $\eta \le 1/2$.

## Proof sketch

Analyse optimistic FTRL as FTRL with an extra predicted loss: the standard be-the-leader argument gives regret at most the regularizer range over $\eta$ plus the sum of inner products of the prediction errors with the consecutive iterate differences, minus the strong-convexity terms. Bounding the inner products by Hölder and Young's inequalities converts them to $\eta \lVert \ell^t - \ell^{t-1}\rVert_\infty^2$ plus a fraction of $\lVert x^{t} - x^{t-1}\rVert_1^2 / \eta$, leaving a negative stability term.

## Depends on

- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)

## Proof depends on

- [The Hedge loss bound](../../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/alg-loss-le.md)

## Sources

- V. Syrgkanis, A. Agarwal, H. Luo, R. E. Schapire, "Fast Convergence of Regularized Learning in Games", NeurIPS 2015, arXiv:1507.00407, Definition 3 and Proposition 7.
- A. Rakhlin, K. Sridharan, "Optimization, Learning, and Games with Predictable Sequences", NeurIPS 2013, arXiv:1311.1869.
