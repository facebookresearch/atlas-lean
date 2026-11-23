# Second derivative along a line

Let $E$ be a real inner product space and let $f : E \to \mathbb{R}$ be $C^2$ at $z$. For every
direction $e \in E$, the second derivative of $f$ at $z$ evaluated at $(e, e)$ is the second
derivative at $0$ of the restriction of $f$ to the line through $z$ in the direction $e$:

$$D^2 f(z)(e, e) = \varphi''(0), \qquad \varphi(t) = f(z + t e).$$

This is the chain-rule computation in the proof of the second-order necessary condition in
Evans's optimization notes.

## Sources

- L. C. Evans, *Mathematics 170: Mathematical Methods for Optimization, Finite Dimensional Optimization*, lecture notes, Spring 2021 version, [math.berkeley.edu/~evans](https://math.berkeley.edu/~evans/), §1.1.2, Theorem 1.1.2 and Remark (ii).
