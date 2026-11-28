# Rock–paper–scissors replicator dynamics and the sign of det A

For the replicator equation on $S_3$ with the rock–scissors–paper matrix

$$A = \begin{pmatrix} 0 & -a_2 & b_3 \\ b_1 & 0 & -a_3 \\ -a_1 & b_2 & 0 \end{pmatrix}, \qquad a_i, b_i > 0,$$

there is a unique rest point $z$ in the interior of $S_3$, which is also the unique Nash equilibrium, and the following are equivalent: (a) $z$ is asymptotically stable; (b) every trajectory starting in the interior $\operatorname{int} S_3$ converges to $z$ (the vertices and edges of $S_3$ are invariant, so no stronger global statement holds); (c) $\det A > 0$; (d) $z\cdot Az > 0$. If $\det A = 0$, all interior orbits are closed orbits around $z$; if $\det A < 0$, every interior orbit other than $z$ has as $\omega$-limit the heteroclinic cycle formed by the three vertices and the edges joining them (Zeeman 1980; Hofbauer and Sigmund 2003, eq. (9) and Theorem 2). Expanding the determinant gives $\det A = b_1 b_2 b_3 - a_1 a_2 a_3$: stability holds exactly when the product of the gains exceeds the product of the losses.

## Depends on

- [Solution of the replicator equation](../../../Biology/population-dynamics/replicator-dynamics/is-solution.md)
- [Rest point of the replicator equation](is-rest-point.md)
- [Symmetric Nash equilibrium of a matrix game](../stability-of-evolutionarily-stable-states/is-nash.md)

## Expansion

1. The replicator equation on $S_3$ and the interior rest point.
2. The function $V(x) = \sum_i z_i \ln x_i$ with $\dot V = z\cdot Ax - x\cdot Ax$, and the relation of its sign to $\det A$.
3. The three cases: convergence of every interior trajectory to $z$, a family of closed orbits, and attraction to the heteroclinic cycle.
4. The equivalence of the four conditions, and the expansion $\det A = b_1b_2b_3 - a_1a_2a_3$.

## Sources

- J. Hofbauer and K. Sigmund, Evolutionary game dynamics, Bull. Amer. Math. Soc. 40 (2003), 479–519, Sec. 2.4, eq. (9) and Theorem 2. <https://doi.org/10.1090/S0273-0979-03-00988-1>
- Original result: E. C. Zeeman, Population dynamics from game theory, in *Global Theory of Dynamical Systems*, Lecture Notes in Math. 819, Springer, 1980, 471–497. <https://doi.org/10.1007/bfb0087009> Theorem 2 of Hofbauer and Sigmund (2003) is attributed there to this paper.
