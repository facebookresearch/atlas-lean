# Nonpositive second derivatives at a local maximum

Let $E$ be a real inner product space and let $f : E \to \mathbb{R}$ be $C^2$ at a local maximum
$z$. Then $D^2 f(z)(e, e) \le 0$ for every direction $e$: the second derivative of $f$ at $z$ is
negative semidefinite.

Evans states the second-order necessary condition for minimizers, $\nabla^2 f(x_0) \succeq 0$,
and notes that it holds at local minima; this is the same statement for local maxima (apply it to
$-f$). The proof restricts $f$ to lines and uses the one-dimensional second-derivative test.

## Informally uses

- [Second derivative along a line](iterated-fderiv-two-apply-eq-deriv-deriv.md): reduces the
  statement to the function $t \mapsto f(z + t e)$ of one variable.

## Sources

- L. C. Evans, *Mathematics 170: Mathematical Methods for Optimization, Finite Dimensional Optimization*, lecture notes, Spring 2021 version, [math.berkeley.edu/~evans](https://math.berkeley.edu/~evans/), §1.1.2, Theorem 1.1.2 and Remark (ii).
