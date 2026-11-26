# Codimension bounds for bifurcations in mass-action networks

**Setting.** A mass-action network with $n$ species and $m$ reactions has the ODE $\dot x = \Gamma\big(\kappa \circ x^{A}\big)$ on $\mathbb{R}^n_{>0}$, where $\Gamma \in \mathbb{R}^{n \times m}$ is the stoichiometric matrix, the columns of $A^\top$ (rows of $A \in \mathbb{R}^{m \times n}$) are the source complexes, $x^A$ is the vector of monomials $x^{A_k}$, and $\kappa \in \mathbb{R}^m_{>0}$ are rate constants. Call it an $(n, m, n)$ network if $\Gamma$ has rank $n$ (no conservation laws) and the matrix $[A \mid \mathbf{1}]$ has rank $n + 1$ (the source complexes affinely span $\mathbb{R}^n$). A bifurcation is **unfolded by the rate constants** if the rate constants provide a versal unfolding of it.

**Theorem 35.** An $(n, m, n)$ mass-action network admits no bifurcation of positive equilibria of codimension greater than $m - 2$ unfolded by its rate constants.

**Theorem 36.** An $(n, n+2, n)$ mass-action network admits no cusp bifurcation unfolded by its rate constants.

**Lemma 37.** A family $\dot y = \gamma \circ f(y, \beta)$ on an open subset of $\mathbb{R}^n$, with parameters $\gamma \in \mathbb{R}^n_{>0}$ (componentwise scaling) and $\beta \in \mathbb{R}$, cannot undergo a cusp bifurcation unfolded by its parameters.

**Classification (planar, quadratic).** For networks with two species, source complexes of molecularity at most two and product complexes of molecularity at most three, with at most four reactions, the generic bifurcations of positive equilibria that occur are exactly fold, Andronov–Hopf, Bogdanov–Takens and Bautin; a unique such network admits a Bautin bifurcation, and a cusp bifurcation in a planar quadratic network requires at least five reactions.

## Expansion

Choose $U$ so that $[A \mid \mathbf{1} \mid U]$ is invertible and split its inverse into an $n \times m$ block $G$, a row $v$ and a block $W$, so that $I - AG = \mathbf{1} v + UW$. In the coordinates $y = \kappa^G \circ x$, monomial combinations of the rate constants are absorbed into the state variables and into a rescaling of time, and the network becomes a family of vector fields depending on only $m - 2$ parameters (Section 2.5); a bifurcation of codimension $c$ needs $c$ independent unfolding parameters, giving Theorem 35. For $m = n + 2$ the family takes the form $\gamma \circ f(y, \beta)$ with a positive componentwise scaling $\gamma$ and one essential parameter $\beta$, and Lemma 37 shows, via the Jacobian and the quadratic Taylor terms, that such a family cannot unfold a cusp. The planar classification is a computer-assisted enumeration of dynamically nonequivalent networks, checking nondegeneracy and transversality conditions for each bifurcation type; rank-one quadratic networks reduce to a one-dimensional quadratic ODE on each stoichiometric class and can only fold.

## Sources

- M. Banaji, B. Boros, J. Hofbauer, "Bifurcations in planar, quadratic mass-action networks with few reactions and low molecularity", Nonlinear Dynamics 112 (2024) 21425–21448, Sections 1 and 2.5, Theorems 35–36, Lemma 37, <https://doi.org/10.1007/s11071-024-10068-1> (PMC11466909).
