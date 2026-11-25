# One-step inequality of mirror descent

Throughout, $E$ is a real normed space with norm $\|\cdot\|$, linear forms $\xi \in E^*$ (continuous linear maps $E \to \mathbb{R}$) carry the dual norm $\|\xi\|_* = \sup_{\|x\| \le 1} \xi(x)$, $\omega \colon E \to \mathbb{R}$ is a distance-generating function with a derivative selection $\omega' \colon E \to E^*$, and $V_x(u)$ is its Bregman divergence. Let $\alpha > 0$, $\xi \in E^*$, and let $x^+$ satisfy, at a point $u$, the first-order optimality condition

$$
\big(\xi - \omega'(x) + \omega'(x^+)\big)(u - x^+) \ge 0
$$

of the prox step $x^+ = \operatorname{argmin}_{v \in X} \{\xi(v) + V_x(v)\}$, together with $V_x(x^+) \ge \tfrac{\alpha}{2} \|x^+ - x\|^2$. Then

$$
V_{x^+}(u) \le V_x(u) + \xi(u - x) + \frac{\|\xi\|_*^2}{2\alpha}.
$$

The proof combines the optimality condition with the [three-point identity](bregman-three-point.md) and bounds $\xi(x - x^+) - V_x(x^+) \le \|\xi\|_* s - \tfrac{\alpha}{2} s^2 \le \|\xi\|_*^2 / (2\alpha)$ with $s = \|x^+ - x\|$. With $\xi = \gamma f'(x)$ it is the step inequality from which every mirror descent rate follows.

## Background

- [Convergence of the subgradient method](../gradient-descent/subgradient-method-rate.md): in the Euclidean setup $V_x(u) = \tfrac12\|u - x\|_2^2$ and this inequality is the distance recursion used there.

## Sources

- A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro, *Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19(4) (2009), 1574–1609; PDF at <https://people.eecs.berkeley.edu/~brecht/cs294docs/week1/09.Nemirovski.pdf>, Section 2.3, Lemma 2.1, inequality (2.33), with the optimality condition and the strong convexity of $V_x$ that its proof (in the appendix) uses taken as hypotheses.
- A. Juditsky and A. Nemirovski, *First order methods for nonsmooth convex large-scale optimization, I: general purpose methods*, in S. Sra, S. Nowozin and S. J. Wright (eds.), *Optimization for Machine Learning*, MIT Press (2011); author PDF at <https://www2.isye.gatech.edu/~nemirovs/MLOptChapterI.pdf>, Section 5.2.3, inequality (5.13).
