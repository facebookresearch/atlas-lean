# Scalar model-reference adaptive tracking

Consider the plant $\dot x = \theta x + u$ with an unknown constant $\theta \in \mathbb{R}$, a bounded piecewise-continuous reference $r$, the reference model $\dot x_m = -a_m x_m + r$ with $a_m > 0$, the control $u = -\hat\theta x - a_m x + r$, and the adaptation law $\dot{\hat\theta} = \gamma\, x\,(x - x_m)$ with $\gamma > 0$. Then for all initial values $x(0)$, $x_m(0)$, $\hat\theta(0)$, the closed loop has a unique solution on $[0, \infty)$, all of $x$, $x_m$, $\hat\theta$ and $u$ are bounded, and the tracking error $e = x - x_m$ tends to $0$.

The result does not claim $\hat\theta(t) \to \theta$: parameter convergence needs a persistence-of-excitation condition on $x$, and fails for example when $r = 0$ and $x(0) = x_m(0) = 0$, where $\hat\theta$ stays at its initial value.

**Proof.** With $\tilde\theta = \hat\theta - \theta$ the error satisfies $\dot e = -a_m e - \tilde\theta x$, and $V = \tfrac12 e^2 + \tfrac{1}{2\gamma}\tilde\theta^2$ satisfies $\dot V = -a_m e^2 - \tilde\theta x e + \tilde\theta x e = -a_m e^2 \le 0$ on the interval of existence. So $e$ and $\hat\theta$ are bounded; $x_m$ is bounded because $r$ is, hence $x = e + x_m$ and $u$ are bounded, and the locally Lipschitz closed loop has no finite escape, so its maximal solution is global. Integrating $\dot V$ gives $\int_0^\infty e^2 \le V(0)/a_m$, and $\frac{d}{dt}e^2 = 2e\dot e$ is bounded, so $e^2$ is uniformly continuous; Barbălat's lemma applied to $e^2$ gives $e \to 0$.

## Proof depends on

- [Barbălat's lemma](barbalat-s-lemma.md): convergence of $e^2$ to $0$
- [Solutions of locally Lipschitz ODEs that leave every compact set](../../../ordinary-differential-equations/maximal-solutions-and-global-existence/ode-maximal-solution-exit-compact.md): global existence from boundedness

## Sources

- B. Farkas and S.-A. Wegner, "Variations on Barbălat's lemma", *American Mathematical Monthly* 123(8), 2016, <https://arxiv.org/abs/1411.1611>, Theorem 1 and its role in Lyapunov-like arguments for nonautonomous and adaptive systems (p. 1). The adaptive tracking law, its Lyapunov function and the counterexample to parameter convergence are derived on the page.
