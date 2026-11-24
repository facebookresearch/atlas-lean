# Real value of the Abel functional of a non-explosive path

Let $\sigma$ be a countable set of states whose σ-algebra contains the singletons,
$q : \sigma \to \mathbb{R}$ positive rates ($q(y) > 0$ for every $y$), $x \in \sigma$, and $\omega$
a sequence of steps with nonnegative clocks whose
[jump times](../non-explosion-of-stochastic-reaction-networks/jump-time.md) tend to $\infty$. Let
$g : \sigma \to \mathbb{R}$ be nonnegative and $a > 0$. Then, reading the
[Abel functional](abel-sum.md) as a real number,

$$A_a g(x, \omega) = a \int_0^\infty e^{-a t} g(X_t)\, dt ,$$

where the integral over $(0, \infty)$ is the Lebesgue (Bochner) integral of the real function
$t \mapsto e^{-a t} g(X_t)$ along the
[path](../non-explosion-of-stochastic-reaction-networks/path.md) $X$ of the chain started at $x$.
If $A_a g(x, \omega) = \infty$, which can happen only when $g$ is unbounded along the chain, both
sides are $0$: the real reading of $\infty$ is $0$, and the integral of a non-integrable function
is $0$. Otherwise this is the
[Laplace transform identity](lintegral-exp-path-eq-abel-sum.md) in real numbers.
