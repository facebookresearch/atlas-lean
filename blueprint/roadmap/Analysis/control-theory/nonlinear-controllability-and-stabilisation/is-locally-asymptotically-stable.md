# Local asymptotic stability of the origin for a vector field

Let $X : E \to E$ be a vector field on a real normed space. The origin is **locally asymptotically stable** for $\dot x = X(x)$ if there is $\delta > 0$ such that for every $\varepsilon > 0$ there is $M > 0$ with $\lVert x(t) \rVert < \varepsilon$ for every solution $x$ of $\dot x = X(x)$ with $\lVert x(0) \rVert < \delta$ and every time $t > M$ in its interval of definition.

The condition is stated for an arbitrary $X$, with no continuity and no assumption that $X(0) = 0$; for such $X$ it can hold for degenerate reasons. For instance, for $X(x) = 1 + x^2$ on $\mathbb{R}$, $\delta = 1$ and $M = 3$ satisfy it for every $\varepsilon$, because every solution starting in $(-1, 1)$ blows up before time $3\pi/4$, although $0$ is not an equilibrium.

For $E$ finite-dimensional, $X$ continuous and $X(0) = 0$, it is Coron, *Control and Nonlinearity* (AMS 2007), Definition 10.6, at the equilibrium $x_e = 0$. Because $X$ is only continuous, the Cauchy problem can have many solutions, and Coron imposes the condition on every maximal solution. The definition here imposes it on every solution defined on an interval $[0, \tau)$, $\tau \in \mathbb{R}$ (with the derivative taken within the interval, one-sided at $0$). Every maximal solution restricts to such solutions, and every solution on $[0, \tau)$ extends to a maximal one (by Peano's theorem and Zorn's lemma), so the two conditions agree. As in Coron's definition, the condition says nothing about a solution that ceases to exist before time $M$; in this setting that is harmless, since for a smaller $\delta$ the definition forces every solution to be global and attracted to $0$. Coron's Theorem 10.8 shows that, in this setting, the definition is equivalent to stability plus attractivity.

## Background

- [Cauchy–Peano existence theorem](../../ordinary-differential-equations/cauchy-peano-exists.md): solutions of continuous vector fields exist but need not be unique.
- [Asymptotic stability of linear ODEs with eigenvalues in the open left half-plane](../../ordinary-differential-equations/lyapunov-s-indirect-method/linear-ode-asymptotic-stability.md): the linear case (Coron, Theorem 10.9).
- [LaSalle's invariance principle](../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md): a classical way to prove asymptotic stability with a Lyapunov function.
