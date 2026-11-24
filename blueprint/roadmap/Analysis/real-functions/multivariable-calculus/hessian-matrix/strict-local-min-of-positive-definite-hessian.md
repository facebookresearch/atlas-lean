# Second-order sufficient condition for a strict local minimum

Let $f : \mathbb{R}^n \to \mathbb{R}$ be twice continuously differentiable on a neighborhood of $x^*$, with $\nabla f(x^*) = 0$ and positive definite Hessian $\nabla^2 f(x^*)$. Then $x^*$ is a strict local minimizer: there is $\delta > 0$ such that $f(x) > f(x^*)$ whenever $0 < \|x - x^*\| < \delta$.

Proof. For $n = 0$ there is nothing to prove, since no $x$ satisfies $0 < \|x - x^*\|$. Otherwise let $\lambda > 0$ be the smallest eigenvalue of $\nabla^2 f(x^*)$. By continuity of the Hessian there is $\delta > 0$ with $\|\nabla^2 f(y) - \nabla^2 f(x^*)\| \le \lambda/2$, hence $h^{\mathsf T}\nabla^2 f(y)h \ge (\lambda/2)\|h\|^2$ for all $h$, whenever $\|y - x^*\| < \delta$. For $0 < \|h\| < \delta$, $g(s) = f(x^* + sh)$ is twice continuously differentiable on $[0, 1]$ with $g'(0) = \nabla f(x^*)^{\mathsf T}h = 0$ and $g''(s) = h^{\mathsf T}\nabla^2 f(x^* + sh)h$, so Taylor's theorem with Lagrange remainder gives $f(x^* + h) - f(x^*) = g''(\xi)/2 \ge (\lambda/4)\|h\|^2 > 0$ for some $\xi \in (0, 1)$.

## Depends on

- [Strict local minimum](../../differential-calculus/local-extrema-and-the-second-derivative-test/is-strict-local-min.md): strict local minimum.

## Background

- [Second-derivative test, necessary condition](is-local-min-hessian-quadratic-nonneg.md): the necessary second-order condition.
- [Strict second-derivative test, minimum version](../../differential-calculus/local-extrema-and-the-second-derivative-test/is-strict-local-min-of-deriv-deriv-pos.md): the one-variable test.

## Sources

- D. P. Bertsekas, *Nonlinear Programming*, lecture slides, MIT 6.252, Spring 2003, Lecture 2, slide "Sufficient conditions for a local min", <https://ocw.mit.edu/courses/6-252j-nonlinear-programming-spring-2003/8bfcb0cea874f9517661e833dba7b874_6252_slides02.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
