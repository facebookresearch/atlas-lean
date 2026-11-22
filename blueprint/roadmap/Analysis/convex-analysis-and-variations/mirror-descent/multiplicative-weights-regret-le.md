# Regret of entropic mirror descent for prediction with expert advice

Let $n \ge 1$, $\gamma > 0$ and let $c_0, c_1, \ldots \in [-1, 1]^n$ be arbitrary loss vectors. Run the multiplicative-weights update from the [uniform point](uniform.md),

$$
x_{t+1, i} = \frac{x_{t,i}\, e^{-\gamma c_{t,i}}}{Z_t}, \qquad Z_t > 0,
$$

with every $x_t$ in the [relative interior of the simplex](pos-simplex.md). Then for every expert $i$ and every $N$,

$$
\sum_{t<N} \big(\langle c_t, x_t\rangle - c_{t,i}\big) \le \frac{\log n}{\gamma} + \frac{\gamma N}{2} ,
$$

and with $\gamma = \sqrt{2\log n / N}$ the regret is at most $\sqrt{2 N \log n}$.

The update is the [entropic prox step](entropy-prox-multiplicative.md), so the [telescoped mirror descent bound](mirror-descent-sum-le.md) applies with the comparator $u = e_i$, a vertex of the simplex: [strong convexity](bregman-entropy-ge.md) holds up to the vertices, $V_{\mathrm{uniform}}(e_i) \le \log n$ ([diameter bound](bregman-entropy-uniform-le.md)) and $\|c_t\|_* \le 1$ ([coordinate bound](norm-le-of-abs-apply-single-le.md)). This is the mirror descent regret bound; it is a different inequality from Hedge's bound $L - L_i \le \eta T + \log n / \eta$, which the Hedge module proves by a potential argument for losses in $[0, 1]$.

## Background

- [Regret of Hedge for losses in the unit interval](../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/regret-le.md): the same update, analysed through the potential $\log \sum_i w_i$.

## Sources

- A. Juditsky and A. Nemirovski, *First order methods for nonsmooth convex large-scale optimization, I: general purpose methods*, in S. Sra, S. Nowozin and S. J. Wright (eds.), *Optimization for Machine Learning*, MIT Press (2011); author PDF at <https://www2.isye.gatech.edu/~nemirovs/MLOptChapterI.pdf>, Section 5.2.3, Proposition 5.1(i), inequality (5.7), in the entropy setup 2(c) of Section 5.7.1.
- A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro, *Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19(4) (2009), 1574–1609; PDF at <https://people.eecs.berkeley.edu/~brecht/cs294docs/week1/09.Nemirovski.pdf>, Section 2.3, Example (the $\ell_1$-setup: $\|\cdot\|_* = \|\cdot\|_\infty$, $D_{\omega,X}^2 = \ln n$, the explicit prox-mapping).
