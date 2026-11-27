# The prox step of the entropy is the multiplicative-weights update

Let $x, x^+$ lie in the [relative interior of the simplex](pos-simplex.md) with

$$
x^+_i = \frac{x_i\, e^{-\gamma c_i}}{Z}
$$

for some $Z > 0$ (necessarily $Z = \sum_i x_i e^{-\gamma c_i}$). Then $x^+$ satisfies the optimality condition of the entropic prox step $x^+ = \operatorname{argmin}_{u \in \Delta_n}\{\gamma \langle c, u\rangle + V_x(u)\}$ with equality:

$$
\big(\gamma c - \omega'(x) + \omega'(x^+)\big)(u - x^+) = 0 \qquad \text{whenever } \textstyle\sum_i u_i = 1 .
$$

Indeed $\log x^+_i = \log x_i - \gamma c_i - \log Z$, so the linear form is the constant $-\log Z$ times $\sum_i (u_i - x^+_i) = 0$. Mirror descent with the entropy on the simplex therefore runs the multiplicative-weights (Hedge, exponentiated gradient) update.

## Background

- [The $\sqrt{T}$ regret bound of Hedge](../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/regret-le-two-sqrt.md): the same update with losses in $[0, 1]$, analysed there through the potential $\log \sum_i w_i$ instead of the Bregman divergence.

## Sources

- A. Juditsky and A. Nemirovski, *First order methods for nonsmooth convex large-scale optimization, I: general purpose methods*, in S. Sra, S. Nowozin and S. J. Wright (eds.), *Optimization for Machine Learning*, MIT Press (2011); author PDF at <https://www2.isye.gatech.edu/~nemirovs/MLOptChapterI.pdf>, Section 5.7.1, the explicit prox-mapping (5.39) for setup 2(c) on the flat simplex.
- A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro, *Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19(4) (2009), 1574–1609; PDF at <https://people.eecs.berkeley.edu/~brecht/cs294docs/week1/09.Nemirovski.pdf>, Section 2.3, Example (the explicit formula for $P_x(y)$).
