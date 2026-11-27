# Lyapunov characterization of evolutionarily stable states for the replicator equation

This node covers the following result. For the replicator equation $\dot x_i = x_i\bigl((Ax)_i - x^{\mathsf T} A x\bigr)$ on the simplex $S_n$, let $V(x) = \prod_i x_i^{p_i}$ for $p \in S_n$; $V$ attains its unique maximum on $S_n$ at $p$, and along solutions $\dot V = V\,(p^{\mathsf T} A x - x^{\mathsf T} A x)$. Then $p$ is an evolutionarily stable strategy if and only if $V$ is a strict local Lyapunov function at $p$, that is $V$ increases strictly along every solution through a point $x \neq p$ of $S_n$ near $p$. Hence every evolutionarily stable strategy is asymptotically stable, both when $p$ lies in the interior of $S_n$ (all $p_i > 0$) and when $p$ lies on its boundary.

## Depends on

- [Solution of the replicator equation](is-solution.md)

## Proof depends on

- [Invariance of the simplex](mem-simplex.md)

## Expansion

A good expansion replaces this node by planned pages beside it, each citing the source below:

1. Definition pages for evolutionarily stable strategies of a symmetric matrix game and for the function $V$, with the conventions of the source.
2. Prerequisites: [solutions of the replicator equation](is-solution.md) and [invariance of the simplex](mem-simplex.md) under it, so that $V$ is evaluated along solutions that stay in $S_n$; and Lyapunov's direct method, that a continuous function with a strict local maximum at a rest point that increases strictly along solutions near it makes the rest point asymptotically stable (a related tool is [LaSalle's invariance principle](../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)).
3. The equivalence between evolutionary stability and the strict local Lyapunov property, with every hypothesis explicit.
4. The corollary as two pages: asymptotic stability of an interior evolutionarily stable strategy, and of one on the boundary of $S_n$.

Nothing beyond the statement above is claimed here.

## Sources

- J. Hofbauer, P. Schuster and K. Sigmund, A note on evolutionary stable strategies and game dynamics, J. Theor. Biol. 81 (1979), 609–612. <https://doi.org/10.1016/0022-5193(79)90058-4>
