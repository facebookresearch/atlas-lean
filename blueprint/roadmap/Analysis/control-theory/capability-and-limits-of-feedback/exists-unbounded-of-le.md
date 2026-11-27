# No feedback stabilises every system with uncertainty at least $3/2 + \sqrt 2$

For $y_{t+1} = f(y_t) + u_t + w_{t+1}$, let $L \ge 3/2 + \sqrt 2$ and $W > 0$. For every feedback law
$u_t = h_t(y_0, \dots, y_t)$ with each $h_t$ Lebesgue measurable, as in the source (so in particular every Borel
measurable law), and every initial value $y_0$, there are
$f : \mathbb R \to \mathbb R$ with generalized Lipschitz quasi-norm $\|f\| \le L$ and a noise sequence with
$|w_t| \le W$ such that the closed loop is unbounded: $\sup_t |y_t| = \infty$. The quasi-norm condition is written as in
[Feedback can stabilise every system with uncertainty below $3/2 + \sqrt 2$](exists-feedback-bdd-above-of-lt.md).

Source: Xie and Guo, IEEE Trans. Automat. Control 45(12) (2000) 2203–2217, as stated in Guo, *Exploring the capability and limits of the feedback mechanism*, Proc. ICM 2002, Vol. III (arXiv:math/0305011), Theorem 4.1(ii); the
original paper was not consulted. Together with the companion page, $3/2 + \sqrt 2$ is the exact radius of the ball of
uncertainty that feedback can handle.

**Differences from the source.** The source does not say how the noise is chosen, so letting the adversary choose it,
as here, is the weakest reading; this choice makes the statement weaker than the source.

## Background

- [Brockett's necessary condition for stabilisation](../nonlinear-controllability-and-stabilisation/brockett-condition-of-is-locally-asympto.md):
  an obstruction of a different kind, to stabilisation of a known nonlinear system by continuous stationary feedback.
