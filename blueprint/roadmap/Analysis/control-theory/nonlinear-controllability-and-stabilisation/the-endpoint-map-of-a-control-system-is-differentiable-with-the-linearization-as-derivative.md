# The endpoint map of a control system is differentiable, with the linearization as derivative

Let $X \subseteq \mathbb{R}^n$ and $U \subseteq \mathbb{R}^m$ be open, let $f : X \times U \to \mathbb{R}^n$ be continuously differentiable, and fix an interval $[\sigma, \tau]$. For an initial state $x$ and an essentially bounded measurable control $\omega : [\sigma, \tau] \to U$ whose values lie in a compact subset of $U$, call $\omega$ admissible for $x$ if the solution $\xi$ of $\dot\xi = f(\xi, \omega)$, $\xi(\sigma) = x$ (absolutely continuous, equation almost everywhere) exists on all of $[\sigma, \tau]$, and let $D$ be the set of such pairs $(x, \omega)$, viewed inside $X \times L^\infty([\sigma, \tau]; \mathbb{R}^m)$. Let $\alpha(x, \omega) = \xi(\tau)$ be the endpoint map. Then:

1. **Openness and continuity.** $D$ is open and $\alpha$ is continuous, as is the map $(x, \omega) \mapsto \xi$ into continuous functions with the uniform norm.
2. **Derivative.** $\alpha$ is continuously Fréchet differentiable on $D$, and its derivative at $(x, \omega)$ in the direction $(\lambda_0, \mu) \in \mathbb{R}^n \times L^\infty$ is $\lambda(\tau)$, where $\lambda$ solves the variational (linearized) equation

    $$\dot\lambda(t) = f_x(\xi(t), \omega(t))\lambda(t) + f_u(\xi(t), \omega(t))\mu(t), \qquad \lambda(\sigma) = \lambda_0 .$$

3. **Rank.** Consequently $\alpha(x, \cdot)$ has a surjective derivative at $\omega$ if and only if the linearized system along $(\xi, \omega)$ is controllable on $[\sigma, \tau]$, that is, $\mu \mapsto \int_\sigma^\tau \Phi(\tau, s)B(s)\mu(s)\, ds$ is onto, with $A(t) = f_x(\xi(t), \omega(t))$, $B(t) = f_u(\xi(t), \omega(t))$ and $\Phi$ the transition matrix of $A$.

**Proof sketch.** For nearby $(x', \omega')$, the difference of the solutions satisfies an integral equation whose right-hand side is Lipschitz in the state on a compact neighborhood of the trajectory, and Grönwall's inequality bounds it by $C(\|x' - x\| + \|\omega' - \omega\|_{L^1})$; this gives part 1. For part 2, the remainder $\xi' - \xi - \lambda$ satisfies a linear equation forced by the second-order Taylor remainder of $f$, which is $o(\|x' - x\| + \|\omega' - \omega\|_\infty)$ uniformly by uniform continuity of $f_x$ and $f_u$ on compact sets, and Grönwall again shows the remainder is of that order. Continuity of the derivative follows from continuous dependence of the variational equation on its coefficients. Part 3 is part 2 with $\lambda_0 = 0$ and the variation-of-constants formula for $\lambda(\tau)$.

## Proof depends on

- [Carathéodory solutions of linear systems with locally integrable inputs](../../ordinary-differential-equations/linear-systems-and-fundamental-matrices/caratheodory-solutions-of-linear-systems-with-locally-integrable-inputs.md): the solution concept and variation of constants for the variational equation

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 2.8, "Linearizations compute differentials": Theorem 1 (the domain is open and the state and path maps are continuous; for $C^1$ systems the endpoint map is $C^1$ with derivative $\lambda(\tau)$ given by the variational equation (2.35); full rank if and only if the linearized reachability map is onto, pp. 57–58). The proof sketch follows the Grönwall estimates of that section.
