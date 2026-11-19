# Bregman divergence (prox-function) of a distance-generating function

For $\omega \colon E \to \mathbb{R}$ on a real normed space and a selection $\omega' \colon E \to E^*$ of its derivative, the **Bregman divergence** (Nemirovski's *prox-function*) is

$$
V_x(u) = \omega(u) - \omega(x) - \omega'(x)(u - x).
$$

It is the gap at $u$ between $\omega$ and its linearization at $x$; for convex $\omega$ it is nonnegative, and for $\omega(x) = \tfrac12 \|x\|_2^2$ on a Euclidean space it is $\tfrac12 \|u - x\|_2^2$. A *proximal setup* consists of a norm and a function $\omega$ that is strongly convex with respect to that norm; mirror descent replaces the squared Euclidean distance of the projected subgradient method by $V$, which adapts the method to the geometry of the feasible set.

## Sources

- A. Juditsky and A. Nemirovski, *First order methods for nonsmooth convex large-scale optimization, I: general purpose methods*, in S. Sra, S. Nowozin and S. J. Wright (eds.), *Optimization for Machine Learning*, MIT Press (2011); author PDF at <https://www2.isye.gatech.edu/~nemirovs/MLOptChapterI.pdf>, Section 5.2.2, equation (5.4).
- A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro, *Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19(4) (2009), 1574–1609; PDF at <https://people.eecs.berkeley.edu/~brecht/cs294docs/week1/09.Nemirovski.pdf>, Section 2.3, equation (2.30).
