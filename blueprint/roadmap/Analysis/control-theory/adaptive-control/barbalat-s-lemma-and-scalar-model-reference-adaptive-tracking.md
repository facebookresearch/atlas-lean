# Barbălat's lemma and scalar model-reference adaptive tracking

1. **Barbălat's lemma.** If $\phi : [0, \infty) \to \mathbb{R}$ is uniformly continuous and $\lim_{t \to \infty}\int_0^t \phi(s)\, ds$ exists and is finite, then $\phi(t) \to 0$ as $t \to \infty$.
2. **Adaptive tracking.** Consider the plant $\dot x = \theta x + u$ with an unknown constant $\theta \in \mathbb{R}$, a bounded piecewise-continuous reference $r$, the reference model $\dot x_m = -a_m x_m + r$ with $a_m > 0$, the control $u = -\hat\theta x - a_m x + r$, and the adaptation law $\dot{\hat\theta} = \gamma\, x\,(x - x_m)$ with $\gamma > 0$. Then for all initial values $x(0)$, $x_m(0)$, $\hat\theta(0)$, the closed loop has a unique solution on $[0, \infty)$, all of $x$, $x_m$, $\hat\theta$ and $u$ are bounded, and the tracking error $e = x - x_m$ tends to $0$.

Part 2 does not claim $\hat\theta(t) \to \theta$: parameter convergence needs a persistence-of-excitation condition on $x$, and fails for example when $r = 0$ and $x(0) = x_m(0) = 0$, where $\hat\theta$ stays at its initial value.

**Proof.** For part 1, suppose $|\phi(t_k)| \ge \varepsilon$ along $t_k \to \infty$. Uniform continuity gives $\delta > 0$ with $|\phi(t) - \phi(t_k)| < \varepsilon/2$ for $|t - t_k| \le \delta$, so $\phi$ keeps the sign of $\phi(t_k)$ there and $\big|\int_{t_k}^{t_k + \delta}\phi\big| \ge \varepsilon\delta/2$, which contradicts the Cauchy criterion for the convergent integral. For part 2, with $\tilde\theta = \hat\theta - \theta$ the error satisfies $\dot e = -a_m e - \tilde\theta x$, and $V = \tfrac12 e^2 + \tfrac{1}{2\gamma}\tilde\theta^2$ satisfies $\dot V = -a_m e^2 - \tilde\theta x e + \tilde\theta x e = -a_m e^2 \le 0$ on the interval of existence. So $e$ and $\hat\theta$ are bounded; $x_m$ is bounded because $r$ is, hence $x = e + x_m$ and $u$ are bounded, and the locally Lipschitz closed loop has no finite escape, so its maximal solution is global. Integrating $\dot V$ gives $\int_0^\infty e^2 \le V(0)/a_m$, and $\frac{d}{dt}e^2 = 2e\dot e$ is bounded, so $e^2$ is uniformly continuous; part 1 applied to $e^2$ gives $e \to 0$.

## Proof depends on

- [Solutions of locally Lipschitz ODEs that leave every compact set](../../ordinary-differential-equations/maximal-solutions-and-global-existence/ode-maximal-solution-exit-compact.md): global existence from boundedness

## Sources

- B. Farkas and S.-A. Wegner, "Variations on Barbălat's lemma", *American Mathematical Monthly* 123(8), 2016, <https://arxiv.org/abs/1411.1611>, Theorem 1 (Barbălat's lemma, a uniformly continuous function with a convergent improper integral tends to $0$) and its role in Lyapunov-like arguments for nonautonomous and adaptive systems (p. 1). The adaptive tracking law, its Lyapunov function and the counterexample to parameter convergence are derived on the page.
