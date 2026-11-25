# Telescoped mirror descent bound

Throughout, $E$ is a real normed space with norm $\|\cdot\|$, linear forms $\xi \in E^*$ (continuous linear maps $E \to \mathbb{R}$) carry the dual norm $\|\xi\|_* = \sup_{\|x\| \le 1} \xi(x)$, $\omega \colon E \to \mathbb{R}$ is a distance-generating function with a derivative selection $\omega' \colon E \to E^*$, and $V_x(u)$ is its Bregman divergence. Let $\alpha > 0$ and $X^o \subseteq X \subseteq E$, and assume $V_x(u) \ge \tfrac{\alpha}{2}\|u - x\|^2$ for $x \in X^o$, $u \in X$. Let $x_0, x_1, \ldots \in X^o$, steps $\gamma_t \in \mathbb{R}$ and arbitrary $g_t \in E^*$ be such that each $x_{t+1}$ satisfies the optimality condition of the prox step $x_{t+1} = \operatorname{argmin}_{u \in X}\{\gamma_t g_t(u) + V_{x_t}(u)\}$:

$$
\big(\gamma_t g_t - \omega'(x_t) + \omega'(x_{t+1})\big)(u - x_{t+1}) \ge 0 \qquad \text{for all } u \in X.
$$

Then for every $u \in X$ and every $N$,

$$
\sum_{t < N} \gamma_t\, g_t(x_t - u) \le V_{x_0}(u) + \frac{1}{2\alpha} \sum_{t < N} \gamma_t^2 \|g_t\|_*^2 .
$$

The vectors $g_t$ are arbitrary, so the bound is a regret bound for online linear optimization; with $g_t$ subgradients of one convex function it yields the rates of mirror descent, and with noisy subgradients the bounds of stochastic mirror descent. The source states strong convexity of $\omega$ in the monotone form $(\omega'(x) - \omega'(x'))(x - x') \ge \|x - x'\|^2$; its proof uses it in the Bregman form assumed here.

## Background

- [The $\sqrt{T}$ regret bound of Hedge](../../../ComputerScience/machine-learning/online-learning-and-boosting/hedge-algorithm/regret-le-two-sqrt.md): linear losses on the simplex, where the multiplicative-weights update of Hedge is the entropic prox step ([entropic prox step](entropy-prox-multiplicative.md)); Hedge's bound follows there from a potential argument, a different inequality from this one.

## Sources

- A. Juditsky and A. Nemirovski, *First order methods for nonsmooth convex large-scale optimization, I: general purpose methods*, in S. Sra, S. Nowozin and S. J. Wright (eds.), *Optimization for Machine Learning*, MIT Press (2011); author PDF at <https://www2.isye.gatech.edu/~nemirovs/MLOptChapterI.pdf>, Section 5.2.3, Proposition 5.1(i), inequality (5.7), with $\alpha = 1$ and iterates indexed from $1$.
- A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro, *Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19(4) (2009), 1574–1609; PDF at <https://people.eecs.berkeley.edu/~brecht/cs294docs/week1/09.Nemirovski.pdf>, Section 2.3, (2.37), the same telescoping with stochastic gradients.
