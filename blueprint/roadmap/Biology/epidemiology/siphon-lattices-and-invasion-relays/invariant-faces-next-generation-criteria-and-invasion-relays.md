# Invariant faces, next-generation criteria and invasion relays

**Siphons and faces.** For a reaction network, a **siphon** is a non-empty set $W$ of species such that every reaction producing a species of $W$ also consumes a species of $W$. For a positive ODE (one representable by mass-action reactions), a set of variables $Z$ is a siphon if and only if the boundary face $F_Z=\{x_i=0,\ i\in Z\}$ is forward invariant (Angeli-De Leenheer-Sontag; Shiu-Sturmfels). Thus invariance of boundary faces, a dynamical notion, is structural. Boundary $\omega$-limit points of interior trajectories lie on faces of critical siphons, and the minimal siphons generate a lattice of invariant faces that organizes the boundary dynamics: disease-free states, single-strain states, and so on.

**Theorem (next-generation criterion on an invariant face).** Let $\dot x=f_x(x,y)$, $\dot y=f_y(x,y)$ on $\mathbb R^m_{\ge0}\times\mathbb R^n_{\ge0}$ be a polynomial positive vector field and suppose the face $F_x=\{x=0\}$ is invariant, i.e. $f_x(0,y)\equiv0$. Then:
1. the mixed block $D_yf_x(0,y)$ vanishes identically, so at every point $(0,y^*)$ of the face
$$J(0,y^*)=\begin{pmatrix}J_x&0\\ *&J_y\end{pmatrix};$$
2. an equilibrium on the face is stable iff both $J_x$ and $J_y$ are stable;
3. if $J_x=F-V$ is a regular splitting ($F\ge0$, $V^{-1}\ge0$), the equilibrium is stable if $\rho(FV^{-1})<1$ and unstable if $\rho(FV^{-1})>1$.

This generalizes the van den Driessche-Watmough next-generation theorem from the disease-free equilibrium to equilibria on any invariant face, with $\rho(FV^{-1})$ acting as an invasion number for the variables freed from zero.

**Relay principle.** Let $(\Sigma',\Sigma)$ be a distance-one cover in the siphon lattice with invader block $\sigma=\Sigma\setminus\Sigma'$ (possibly several species at once), and let $E^*$ be an equilibrium on the face $F_\Sigma$. The transversal linearization is the single Metzler block $M_\sigma(E^*)=D_{x_\sigma}f_\sigma(\bar x^*,0)$, and the **shared inequality**
$$\alpha\big(M_\sigma(E^*)\big)>0\qquad(\alpha=\text{spectral abscissa}),$$
equivalently an invasion number $R_\sigma(E^*)>1$, is simultaneously the condition for $E^*$ to lose transversal stability and the condition for a successor equilibrium with $x_\sigma>0$ to appear on the adjacent face $F_{\Sigma'}$, via a siphon-induced transcritical bifurcation. Stability transitions along the lattice therefore come in relays, which can be checked algorithmically (exact face equilibria plus symbolic invasion numbers) when the equilibria are rational.

## Depends on

- [Next-generation matrix and the basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/README.md)

## Expansion

Face invariance means every monomial of $f_x$ contains some $x_p$, so $\partial f_x/\partial y$ also contains a factor of $x$ and vanishes on the face; the Jacobian is block triangular and its spectrum splits into the transversal block $J_x$ and the within-face block $J_y$. For Metzler $J_x=F-V$ with $V$ an M-matrix, $\alpha(F-V)$ and $\rho(FV^{-1})-1$ have the same sign (Varga), which is the classical next-generation argument. The relay statement is the observation that the same matrix $M_\sigma$ governs both transversal instability and the bifurcating branch, so the apparent coincidence between "resident loses stability" and "invader equilibrium exists" in multi-strain models is one inequality. Relay transitions differ from generic transcritical bifurcations because the exchange of stability is forced by face invariance and can involve whole blocks of species. The framework is illustrated on multi-strain contagion models of rumor spreading, where for one variant all boundary and interior equilibria are explicit and the relay table is fully verified, and rank-one perturbation (matrix determinant lemma) handles a waning-impulse variant.

## Sources

- F. Avram, R. Adenane, A.-D. Halanay, "Relay transitions and invasion thresholds in multi-strain rumor models: a chemical reaction network approach", arXiv:2603.01186 (2026), Section 3 (relay test, shared inequality, algorithm), Section 6 (Corollary 1), Section 7 (NGM theorem for forward invariant faces) and Section 8 (siphons and boundary omega-limit points), <https://doi.org/10.48550/arXiv.2603.01186>.
