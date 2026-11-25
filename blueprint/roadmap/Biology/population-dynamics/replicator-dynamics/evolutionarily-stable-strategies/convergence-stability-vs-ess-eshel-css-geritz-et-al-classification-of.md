# Convergence stability, evolutionary stability and evolutionary branching

In adaptive dynamics with one-dimensional strategies, let $s_x(y)$ be the invasion fitness of a rare mutant $y$ in a resident population $x$, smooth, with $s_x(x) = 0$, and let $D(x) = \partial_y s_x(y)|_{y = x}$ be the selection gradient; $x^*$ is singular if $D(x^*) = 0$. With all second derivatives evaluated at $x = y = x^*$ and generic strict inequalities, $x^*$ is a local strict Nash equilibrium (evolutionarily stable) if $\partial_y^2 s < 0$, and convergence stable if $D'(x^*) = \partial_x\partial_y s + \partial_y^2 s < 0$; strategies that are both are continuously stable strategies (Eshel 1983), and an evolutionarily stable strategy need not be convergence stable (Hofbauer and Sigmund 2003, Sec. 4.2, in the variables $W(h, s) = A(s + h, s) - A(s, s)$). Since $s_x(x) \equiv 0$ gives $\partial_x^2 s + 2\partial_x\partial_y s + \partial_y^2 s = 0$ on the diagonal, convergence stability is equivalent to $\partial_y^2 s < \partial_x^2 s$. In the notation $2c_{11} = \partial_x^2 s$, $2c_{22} = \partial_y^2 s$ of Metz, Geritz, Meszéna, Jacobs and van Heerwaarden (1996, Sec. 3.2), monomorphic substitutions approach $x^*$ when $c_{22} < c_{11}$, nearby dimorphisms exist (mutual invasibility) when $c_{22} > -c_{11}$, and the singular points are evolutionary repellers ($c_{22} > c_{11}$), evolutionary attractors ($c_{22} < c_{11}$, $c_{22} < 0$) or branching points ($0 < c_{22} < c_{11}$): convergence stable but not evolutionarily stable.

## Expansion

1. The model: invasion fitness, the selection gradient and singular strategies, with smoothness hypotheses.
2. The identity $\partial_x^2 s + 2\partial_x\partial_y s + \partial_y^2 s = 0$ at $x^*$ from $s_x(x) \equiv 0$, and the equivalent forms of the conditions.
3. Convergence stability as stability of the adaptive dynamics $\dot x = k\, D(x)$ at $x^*$.
4. Mutual invasibility and the branching criterion, with the geometry of the dimorphic region (Sec. 3.2 of Metz et al.).
5. The finer classification of pairwise invasibility plots by these inequalities (Geritz, Kisdi, Meszéna and Metz 1998), as a separate statement.

## Sources

- J. Hofbauer and K. Sigmund, Evolutionary game dynamics, Bull. Amer. Math. Soc. 40 (2003), 479–519, Sec. 4.2, eq. (77). <https://doi.org/10.1090/S0273-0979-03-00988-1>
- J. A. J. Metz, S. A. H. Geritz, G. Meszéna, F. J. A. Jacobs and J. S. van Heerwaarden, Adaptive dynamics, a geometrical study of the consequences of nearly faithful reproduction, in S. J. van Strien and S. M. Verduyn Lunel (eds.), *Stochastic and Spatial Structures of Dynamical Systems*, North-Holland, Amsterdam, 1996, 183–231, Secs. 3.2.4–3.2.5, eq. (3.14).
- Original result: I. Eshel, Evolutionary and continuous stability, J. Theor. Biol. 103 (1983), 99–111. <https://doi.org/10.1016/0022-5193(83)90201-1> The continuously stable strategy follows Hofbauer and Sigmund (2003), Sec. 4.2.
