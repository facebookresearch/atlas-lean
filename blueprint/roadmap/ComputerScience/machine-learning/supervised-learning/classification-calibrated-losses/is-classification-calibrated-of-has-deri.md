# Convex losses with negative slope at 0 are classification-calibrated

Let $\varphi : \mathbb{R} \to [0, \infty)$ be convex and differentiable at $0$ with $\varphi'(0) < 0$. Then $\varphi$ is classification-calibrated.

For $\eta > 1/2$ the conditional risk $C_\eta$ is convex with $C_\eta'(0) = (2\eta - 1)\varphi'(0) < 0$; so some $\varepsilon > 0$ has $C_\eta(\varepsilon) < C_\eta(0)$, convexity gives $C_\eta(\alpha) \ge C_\eta(0)$ for every $\alpha \le 0$, and therefore $H(\eta) \le C_\eta(\varepsilon) < C_\eta(0) \le H^-(\eta)$. The case $\eta < 1/2$ follows by the symmetry $\eta \leftrightarrow 1 - \eta$. The hinge loss $\max(0, 1 - \alpha)$, the exponential loss $e^{-\alpha}$ and the logistic loss are examples.

This is the sufficiency half of Bartlett, Jordan and McAuliffe's Theorem 4, part 1, which states the equivalence for convex $\varphi$.

## Informally uses

- [Symmetry of the optimal risks](opt-risk-one-sub.md): builds on, for the case $\eta < 1/2$.

## Sources

- P. L. Bartlett, M. I. Jordan and J. D. McAuliffe, *Convexity, classification, and risk bounds*, Journal of the American Statistical Association 101 (2006) 138–156; numbering of the technical report version <https://www.stat.berkeley.edu/~bartlett/papers/bjm-ccrb-05.pdf>, Theorem 4, part 1, and Examples 1 and 4.
