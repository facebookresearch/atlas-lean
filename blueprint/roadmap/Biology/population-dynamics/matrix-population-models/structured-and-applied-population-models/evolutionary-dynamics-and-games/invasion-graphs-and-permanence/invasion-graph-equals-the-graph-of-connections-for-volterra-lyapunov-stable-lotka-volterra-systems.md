# Invasion graph equals the graph of connections for Volterra–Lyapunov stable Lotka–Volterra systems

Consider the Lotka–Volterra system on $\mathbb R^n_{\ge 0}$

$$\dot u_i = u_i\Bigl(b_i + \sum_{j=1}^n a_{ij} u_j\Bigr), \qquad i = 1,\dots,n,$$

with $A = (a_{ij})$ **Volterra–Lyapunov stable**: there is a positive diagonal matrix $D$ such that $DA + A^{\mathsf T} D$ is negative definite. Then every principal submatrix of $A$ is Volterra–Lyapunov stable, solutions exist globally and depend continuously on data, and for every $b$ there is a unique globally asymptotically stable stationary point (GASS) in $\mathbb R^n_{\ge 0}$; the same holds for the restriction to any face of the orthant.

A set $I \subseteq \{1,\dots,n\}$ is an **admissible community** if there is an equilibrium $u^*$ with $u^*_i > 0 \iff i \in I$ (it is unique); $\mathcal E$ denotes the family of admissible communities. The **invasion rate** of species $i$ into $I$ is $r_i(I) = b_i + \sum_{j \in I} a_{ij} u^*_j$ (so $r_i(\emptyset) = b_i$ and $r_i(I) = 0$ for $i \in I$); for $i \notin I$ these are exactly the eigenvalues of the linearisation at $u^*$ transverse to the face of $I$, while the eigenvalues within the face have negative real part. The **invasion graph** on $\mathcal E$ has an edge $I_1 \to I_2$ iff $r_j(I_1) > 0$ for all $j \in I_2 \setminus I_1$ and $r_j(I_2) < 0$ for all $j \in I_1 \setminus I_2$. The **graph of connections** has an edge $I_1 \to I_2$ iff some solution tends to the equilibrium of $I_1$ as $t \to -\infty$ and to that of $I_2$ as $t \to +\infty$.

1. **Invasion leads to the GASS of the enlarged community.** If $I \in \mathcal E$ and $J \supseteq I$ satisfies $r_j(I) > 0$ for every $j \in J \setminus I$, then there is a solution from the equilibrium of $I$ (as $t \to -\infty$) to the GASS of the system restricted to $J$.
2. **Edges are realised.** If the invasion graph has an edge $I_1 \to I_2$, then the equilibrium of $I_2$ is the GASS of the system restricted to $I_1 \cup I_2$, and a heteroclinic connection from $I_1$ to $I_2$ exists.
3. **Coincidence.** The invasion graph is a subgraph of the graph of connections. If moreover every admissible equilibrium is hyperbolic ($r_i(J) \ne 0$ for all $J \in \mathcal E$, $i \notin J$), the two graphs coincide.

## Expansion

At the equilibrium of $I$, the Jacobian is block triangular: the block on $I$ is $\operatorname{diag}(u^*_I) A_{II}$, stable because $A_{II}$ is Volterra–Lyapunov (hence $D$-) stable, and the transverse block is diagonal with entries $r_i(I)$. If $r_j(I) > 0$ on $J \setminus I$, the unstable manifold contains points $u^* + \varepsilon(y, \mathbf 1_{J \setminus I}) + O(\varepsilon^2)$ lying in the interior of the face of $J$; on that face the restricted system has a unique GASS, which attracts the orbit, giving item 1. For item 2, apply item 1 with $J = I_1 \cup I_2$; if the GASS of $J$ were not the equilibrium $u^k$ of $I_2$, the conditions $r_j(I_2) < 0$ on $I_1 \setminus I_2$ together with stability inside the face make $u^k$ hyperbolic and locally attracting in the face of $J$, contradicting global attraction to a different point. Item 3 combines item 2 with the general fact that every heteroclinic connection between equilibria is an edge of the invasion graph. In practice the invasion graph, computed from sign tables alone without solving linear complementarity problems, gives the full assembly network of the community.

## Sources

- P. Almaraz, P. Kalita, J. A. Langa, F. Soler-Toscano, "Structural stability of invasion graphs for Lotka–Volterra systems", *Journal of Mathematical Biology* (2024), Sections 2–4 (Definitions 1–3, 9, 12, 17, Theorems 5, 8, Lemmas 10–11, 16, Theorem 18, Corollary 22, Theorem 23, Corollary 24, Remark 25), <https://doi.org/10.1007/s00285-024-02087-8> (PMC11023985).
