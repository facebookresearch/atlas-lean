# Lyapunov's indirect method (linearized stability), conditional decay form

Let $\iota$ be a finite set and give $\mathbb{R}^\iota$ the maximum norm. A real $\iota \times \iota$ matrix is Hurwitz if all its complex eigenvalues have negative real part. Let $f : \mathbb{R}^\iota \to \mathbb{R}^\iota$ satisfy $f(x^\star) = 0$ and be differentiable at $x^\star$ with Hurwitz Jacobian matrix $A$. Then there are $\delta, C, \alpha > 0$ such that every curve $x : \mathbb{R} \to \mathbb{R}^\iota$ that is differentiable at every $t \ge 0$ with $x'(t) = f(x(t))$ and satisfies $\|x(0) - x^\star\| < \delta$ obeys

$$
\|x(t) - x^\star\| \le C e^{-\alpha t} \|x(0) - x^\star\| \qquad (t \ge 0).
$$

This is conditional on the solution being defined on all of $[0, \infty)$; it does not assert existence of solutions, so it is not by itself local exponential stability (compare Khalil 2002, Theorem 4.7, which assumes $f$ continuously differentiable and concludes asymptotic stability).
