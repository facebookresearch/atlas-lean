# Characteristic-based feedback theorems for monotone input-output systems

**Monotone input-output systems.** Consider $\dot x = f(x, u)$, $y = h(x)$ with states in $X \subseteq \mathbb{R}^n$, inputs in $U \subseteq \mathbb{R}^m$ and outputs in $Y \subseteq \mathbb{R}^p$, each ordered by a closed, pointed cone with nonempty interior. The system is monotone if $h$ preserves order and, for initial states $\xi_1 \preceq \xi_2$ and inputs $u_1(t) \preceq u_2(t)$ for all $t \ge 0$, the solutions satisfy $x(t, \xi_1, u_1) \preceq x(t, \xi_2, u_2)$ for all $t > 0$. For orthant orders, with sign-definite partial derivatives of $f$ and $h$ and convex $X$, this holds for some choice of orthants if and only if the signed graph on the $n + m + p$ state, input and output nodes (self-loops of the states ignored) has no negative undirected loop. The system has a characteristic $k$ if for each constant input $u$ there is a globally asymptotically stable steady state $k_X(u)$, and then $k(u) = h(k_X(u))$.

Below, inputs and outputs are scalar, and two such systems with characteristics $k$ and $g$ are interconnected by feeding the output of each into the input of the other.

**Theorem (positive feedback).** Let both systems be monotone with increasing characteristics $k$ (first system, $y = k(u)$) and $g$ (second system, $u = g(y)$). Steady states of the closed loop correspond bijectively to intersection points of the graphs of $k$ and $g^{-1}$. Label a non-tangential intersection $S$ if the slope of $k$ there is smaller than that of $g^{-1}$, and $U$ if it is larger. Assume that each system has, for every constant input, a unique globally asymptotically stable steady state with nonsingular state Jacobian, that no intersection is tangential, that the closed loop is strongly monotone and that all its solutions are bounded. Then the solution from almost every initial state converges to a steady state labeled $S$ (Angeli and Sontag 2004, Theorem 3).

**Theorem (negative feedback; small-gain theorem).** Let the first system be monotone with characteristic $k$ and the second be anti-monotone (inhibition included in its output) with characteristic $g$. If all closed-loop solutions are bounded and the scalar iteration

$$u_{j+1} = g\bigl(k(u_j)\bigr)$$

has a globally attractive fixed point (equivalently, it has no nontrivial period-two orbit), then the closed loop has a globally attracting steady state. The conclusion persists with constant delays, $u(t) = y(t - h)$, and with time-varying or state-dependent delays $h(t)$ such that $t - h(t) \to \infty$, and for the reaction-diffusion version with Neumann boundary conditions, whose solutions all converge to a unique spatially uniform state.

## Expansion

When one block is memoryless, the closed loop reduces to a scalar equation in which $u$ decreases where the graph of $g^{-1}$ lies above $k$ and increases where it lies below, so trajectories leave $U$ points and approach $S$ points; a sigmoidal characteristic with linear feedback gives three intersections and two stable states. The positive-feedback theorem shows that this planar picture remains valid for monotone subsystems of any dimension, by applying Hirsch's generic convergence theorem to the strongly monotone closed loop. Without monotonicity the picture fails: a two-dimensional activator-inhibitor system with unit feedback has a sigmoidal characteristic predicting two stable states, yet its phase plane shows two unstable spirals, a saddle and a limit cycle; its influence graph contains a negative loop.

Both theorems need only the monotonicity of each block and the plots of their steady-state input-output curves, which can be interpolated from dose-response data, not the rate equations. For a quasi-steady-state MAPK cascade made monotone by eliminating two conserved species, a sigmoidal characteristic with linear positive feedback $u = gy$ yields a unique high state for $g = 1/0.98$, bistability for $g = 1/2.1$ and a unique low state for $g = 1/6$, and the full saddle-node bifurcation diagram in $g$ follows from the characteristic alone. In the negative-feedback case, a period-two orbit of the iteration signals possible oscillations once delays are large, as in Goldbeter's circadian model, where a Hopf bifurcation appears.

## Depends on

- [Balanced species graphs and orthant monotonicity](balanced-species-graphs-and-orthant-monotonicity.md)

## Sources

- E. D. Sontag, "Monotone and near-monotone biochemical networks", Systems and Synthetic Biology 1 (2007) 59 to 87, section "I/O monotone systems" (Equation 1, definitions and graphical orthant test), section "Positive feedback and possible multistability" (characteristics), section "Positive feedback and multistability in monotone I/O systems" (Equations 2 and 3, $S$ and $U$ labels, "A cautionary counterexample", "A general theorem", MAPK example) and section "Negative feedback and possible oscillations" (small-gain theorem with delays and diffusion, testosterone and circadian examples), <https://doi.org/10.1007/s11693-007-9005-9>, PMCID PMC2533521.
- D. Angeli, E. D. Sontag, "Multi-stability in monotone input/output systems", Systems & Control Letters 51 (2004) 185–202, Theorem 3.
