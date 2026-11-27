# Linear characterization of ZD strategies in public goods games

In the iterated linear public goods game with $n \ge 3$ players (contribution $c$, factor $1 < r < n$), a memory-one strategy $\mathbf p = (p_{S,j})_{S \in \{C,D\},\, 0 \le j \le n-1}$ is a [zero-determinant strategy](zero-determinant-strategies-in-multiplayer-social-dilemmas.md) only if

$$p_{S,j+1} - p_{S,j} = p_{S,j} - p_{S,j-1} \quad (S \in \{C, D\},\ 1 \le j \le n-2), \qquad p_{C,j+1} - p_{D,j+1} = p_{C,j} - p_{D,j} \quad (0 \le j \le n-2).$$

Conversely, a strategy satisfying these equalities is a ZD strategy except on a lower-dimensional set where the parametrization degenerates (see the expansion). So $p_{C,j}$ and $p_{D,j}$ are affine in $j$ with a common slope, and the ZD strategies fill a 3-dimensional subspace of the $2n$-dimensional space of memory-one strategies. For reactive strategies ($p_{C,j} = p_{D,j} = p_j$) with $n = 3$, the condition is $p_2 - p_1 = p_1 - p_0$: a plane in the cube $[0,1]^3$ with corners ALLD $(0,0,0)$, proportional Tit-for-Tat $(1, \tfrac12, 0)$, ALLC $(1,1,1)$ and anti-Tit-for-Tat $(0, \tfrac12, 1)$. Extortionate strategies lie on the edge from proportional Tit-for-Tat to ALLD (they have $p_0 = 0$), and generous ones on the edge from proportional Tit-for-Tat to ALLC (they have $p_{n-1} = 1$).

## Depends on

- [Zero-determinant strategies in multiplayer social dilemmas](zero-determinant-strategies-in-multiplayer-social-dilemmas.md)

## Proof sketch

In the linear public goods game $a_j = rc(j+1)/n - c$ and $b_j = rcj/n$ are affine in $j$ with slope $rc/n$, while $b_{j+1} - a_j = c$ and $b_j - a_{j-1} = c$ are constant. Substituting in the ZD formulas, $p_{C,j}$ and $p_{D,j}$ are affine in $j$ with the common slope $\phi c\,[\tfrac{1}{n-1} - (1-s)\tfrac rn]$, which gives both families of equalities. Conversely, a vector satisfying them is fixed by three numbers: the common slope, $p_{D,0} = \phi(1-s)l$ and $p_{C,0} - p_{D,0} = 1 + \phi c[(1-s)(1 - r/n) - 1]$. The slope and $p_{C,0} - p_{D,0}$ are linear in $(\phi, \phi(1-s))$ with determinant $c^2(r-1)/(n-1) \ne 0$, so they determine $\phi$ and $\phi(1-s)$; then $p_{D,0}$ determines $l$ whenever $s \ne 1$. The exceptions are $\phi = 0$ (the strategy that always repeats its own last move) and $\phi(1-s) = 0$ with $p_{D,0} \ne 0$ (Eq. (5) and Appendix A.3 of the source).

## Sources

- C. Hilbe, B. Wu, A. Traulsen, M. A. Nowak, "Evolutionary performance of zero-determinant strategies in multiplayer games", Journal of Theoretical Biology (2015), <https://doi.org/10.1016/j.jtbi.2015.03.032> (PMC4425415).
