# Regret bounded by variation in utilities for optimistic algorithms

An online learning algorithm on the simplex with fixed parameters (for instance a fixed step size $\eta$) satisfies the RVU property with parameters $\alpha > 0$ and $0 < \beta \le \gamma$ if against every loss sequence

$$
\mathrm{Reg}_T \le \alpha + \beta \sum_{t = 1}^T \lVert \ell^t - \ell^{t-1} \rVert_\infty^2 - \gamma \sum_{t = 1}^T \lVert x^t - x^{t-1} \rVert_1^2 .
$$

Optimistic follow-the-regularized-leader with step size $\eta$, a regularizer $R$ that is $1$-strongly convex with respect to a norm $\lVert\cdot\rVert$, and the previous loss $\ell^{t-1}$ as its prediction of $\ell^t$ (so that $x^t$ minimizes $\langle x, \sum_{s < t} \ell^s + \ell^{t-1} \rangle + R(x)/\eta$) satisfies the bound above, with $\lVert\cdot\rVert_\infty$ replaced by the dual norm $\lVert\cdot\rVert_*$ for the loss differences and $\lVert\cdot\rVert_1$ by $\lVert\cdot\rVert$ for the iterate differences, with $\alpha = (\max R - \min R)/\eta$, $\beta = \eta$ and $\gamma = 1/(4\eta)$. Optimistic Hedge is the case of the entropy regularizer, which is $1$-strongly convex with respect to $\lVert\cdot\rVert_1$, with $\alpha = (\log n)/\eta$, $\beta = \eta$ and $\gamma = 1/(4\eta)$. The condition $\beta \le \gamma$ of the definition, $\eta \le 1/(4\eta)$, holds exactly when $\eta \le 1/2$, so these algorithms have the RVU property for every fixed step size $\eta \le 1/2$. Syrgkanis et al. (Definition 3) state the property for vanishing-regret algorithms; here only the inequality is asserted, because a fixed-step optimistic algorithm need not have $o(T)$ regret against every loss sequence.

## Proof sketch

Analyse optimistic FTRL as FTRL with an extra predicted loss: the standard be-the-leader argument gives regret at most the regularizer range over $\eta$ plus the sum of inner products of the prediction errors with the consecutive iterate differences, minus the strong-convexity terms. Bounding the inner products by Hölder and Young's inequalities converts them to $\eta \lVert \ell^t - \ell^{t-1}\rVert_\infty^2$ plus a fraction of $\lVert x^{t} - x^{t-1}\rVert_1^2 / \eta$, leaving a negative stability term. A fixed step size does not give vanishing regret: for two actions with alternating losses $(1, 0), (0, 1), (1, 0), \dots$ and $\ell^0 = 0$, optimistic Hedge puts weight $1/(1 + e^{-\eta})$ on the losing action at every odd round after the first and weight $1/(1 + e^{-2\eta})$ at every even round, so its expected loss exceeds $T/2$, the loss of either fixed action, by a constant times $T$. For losses in $[0, 1]^n$, dropping the negative term and choosing $\eta = \min\{1/2, \sqrt{(\log n)/T}\}$ when $T$ is known gives regret $O(\sqrt{T\log n} + \log n)$ from the same inequality.

## Depends on

- [Optimistic Hedge in a repeated normal-form game](optimistic-hedge-in-games.md)

## Proof depends on

- [The Hedge loss bound](../../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/alg-loss-le.md)

## Sources

- V. Syrgkanis, A. Agarwal, H. Luo, R. E. Schapire, "Fast Convergence of Regularized Learning in Games", NeurIPS 2015, arXiv:1507.00407, Definition 3 and Proposition 7.
- A. Rakhlin, K. Sridharan, "Optimization, Learning, and Games with Predictable Sequences", NeurIPS 2013, arXiv:1311.1869.
