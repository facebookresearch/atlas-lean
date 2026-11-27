# Exponential stabilisation of controllable linear systems

Let $A \in \mathbb{R}^{n \times n}$ and $B \in \mathbb{R}^{n \times m}$ satisfy the Kalman rank condition. Then there are $K \in \mathbb{R}^{m \times n}$ and constants $M, \alpha > 0$ with $\lVert e^{t (A + BK)} v \rVert \le M e^{-\alpha t} \lVert v \rVert$ for all $t \ge 0$ and $v \in \mathbb{R}^n$ (sup norm). Hence every solution of the closed-loop system $\dot x = (A + BK) x$ decays exponentially, and $0$ is globally asymptotically stable for it.

This is Coron, *Control and Nonlinearity* (AMS 2007), Corollary 10.12 (stated there as global asymptotic stability of the closed loop; the exponential bound is the form stated here). Equivalently, every controllable linear system is globally asymptotically stabilisable by continuous stationary feedback laws.

## Informally uses

- [Controllable linear systems have a Hurwitz closed loop](exists-is-hurwitz-add-mul.md): the feedback.
- [Exponential decay of a Hurwitz semigroup](../../ordinary-differential-equations/lyapunov-s-indirect-method/exists-norm-exp-smul-mul-vec-le.md): Coron's Theorem 10.9, in exponential form.
