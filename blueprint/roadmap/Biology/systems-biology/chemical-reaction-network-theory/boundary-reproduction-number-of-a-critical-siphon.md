# Boundary reproduction number of a critical siphon

**Setting.** A chemical reaction network $(\mathcal S,\mathcal R)$ with species $X_1,\dots,X_n$ evolves by $\dot{\mathbf x}=\mathbf f(\mathbf x)$ under kinetics satisfying the standard positivity and monotonicity assumptions. A set $\mathcal X\subseteq\mathcal S$ is a *siphon* if every reaction producing a species of $\mathcal X$ also consumes a species of $\mathcal X$; its complement $\mathcal Y$ is the antisiphon. The siphon is *critical* if no nonnegative conservation vector is supported inside $\mathcal X$. Order coordinates as $\mathbf x=(\tilde{\mathbf x},\tilde{\mathbf y})$ with $\tilde{\mathbf x}$ the siphon species, so the face $\{\tilde{\mathbf x}=0\}$ is forward invariant and contains the $\mathcal X$-free boundary steady states $\mathbf x^*=(\mathbf 0,\tilde{\mathbf y}^*)$. Split the siphon dynamics as $\dot{\tilde{\mathbf x}}=\mathcal F(\tilde{\mathbf x},\tilde{\mathbf y})-\mathcal V(\tilde{\mathbf x},\tilde{\mathbf y})$ with $\mathcal F\ge0$ (production of siphon species, the analogue of new infections), let $F=\partial_{\tilde{\mathbf x}}\mathcal F(\mathbf x^*)$ and $V=\partial_{\tilde{\mathbf x}}\mathcal V(\mathbf x^*)$, and define the *boundary reproduction number*

$$\mathscr R_{\mathbf x^*}=\rho(FV^{-1}).$$

**Theorem 1.** Let $\mathcal X$ be a critical siphon, $\mathbf x^*$ an $\mathcal X$-free boundary steady state and $F,V$ from an admissible splitting.
(a) If the network has no conservation laws and the Jacobian of the antisiphon dynamics with respect to $\tilde{\mathbf y}$ at $\mathbf x^*$ is Hurwitz, then $\mathbf x^*$ is locally asymptotically stable if $\mathscr R_{\mathbf x^*}<1$ and unstable if $\mathscr R_{\mathbf x^*}>1$.
(b) If the number of antisiphon species equals the number $n-s$ of independent conservation laws and the conservation matrix restricted to $\mathcal Y$, $W_{\mathcal Y}$, is invertible, then $\mathbf x^*=(\mathbf 0,W_{\mathcal Y}^{-1}\boldsymbol\Lambda)$ is the unique steady state in its stoichiometric compatibility class and is locally asymptotically stable relative to that class if $\mathscr R_{\mathbf x^*}<1$ and unstable if $\mathscr R_{\mathbf x^*}>1$.

**Theorem 2.** If $F\ge0$ and $V$ is block triangularizable with nonpositive off-diagonal blocks and diagonal blocks $A_i$ that are $Z$-matrices with $\mathbb 1^{\mathsf T}A_i\ge0$, then $V^{-1}\ge0$.

**Theorem 3.** A splitting with these properties can be read from the $\mathcal X$-reduced network (siphon species plus $\emptyset$, an edge from reactant to product species): it suffices that the $\mathcal F$-part is nonempty and contains all self-loops, and that $\{\emptyset\}$ is the unique terminal strongly connected component of the $\mathcal V$-part, together with a mild condition on the remaining edges.

## Depends on

- [R0 as a threshold for the linearized infected subsystem](../../epidemiology/next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

At $\mathbf x^*$ the Jacobian is block triangular because siphon species cannot be produced without siphon reactants: its eigenvalues are those of $F-V$ (siphon block) and of the antisiphon block. When $F\ge0$ and $V$ is a nonsingular M-matrix, $F-V$ is Hurwitz iff $\rho(FV^{-1})<1$, the van den Driessche–Watmough next-generation argument; Theorems 2 and 3 provide checkable graph conditions that make $V$ an M-matrix even with dissociation reactions $X_1\to X_2+X_3$ inside the siphon, which the epidemic-model setting excluded. Conservation laws are handled by restricting to the compatibility class, where the invertibility of $W_{\mathcal Y}$ pins down the antisiphon concentrations. For the EnvZ–OmpR osmoregulation network this gives $\mathscr R_{\mathbf x^*}=k_5Y_{tot}/k_2$, so the boundary state is stable iff $Y_{tot}<k_2/k_5$.

## Sources

- M. D. Johnston, F. Avram, "The Boundary Reproduction Number for Determining Boundary Steady State Stability in Chemical Reaction Systems", *Journal of Mathematical Biology* 92(2) (2026), 29, Theorems 1–3, <https://doi.org/10.1007/s00285-026-02351-z> (preprint arXiv:2506.01606).
