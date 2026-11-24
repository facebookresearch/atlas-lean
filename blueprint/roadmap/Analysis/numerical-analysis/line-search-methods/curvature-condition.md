# Wolfe curvature condition

Let $E$ be a real Hilbert space (for instance $\mathbb{R}^n$) and $f : E \to \mathbb{R}$. A step length $\alpha$ along $d$ from $x$ satisfies the *Wolfe curvature condition* with
constant $\sigma$ if

$$\nabla f(x + \alpha d)^\top d \ge \sigma\, \nabla f(x)^\top d.$$

For a descent direction and $\sigma < 1$ this says that the directional derivative has increased
by a definite fraction, which rules out steps that are too short. The source states the condition
with a strict inequality; the non-strict form used here is weaker, so results assuming it apply to
both.

## Sources

- Y. H. Dai and Y. Yuan, *A nonlinear conjugate gradient method with a strong global convergence property*, SIAM J. Optim. 10 (1999), 177–182, condition (1.10).
