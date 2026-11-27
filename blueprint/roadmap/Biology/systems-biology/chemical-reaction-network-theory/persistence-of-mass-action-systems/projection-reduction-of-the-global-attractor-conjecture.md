# Projection reduction of the global attractor conjecture

**Setting.** For a mass-action reaction network on species set $S$, restrict the dynamics to a box (a *confined* reaction system: the rate constants may vary within positive bounds, giving a differential inclusion rather than a single ODE) and push it forward to the open hypercube $(0,1)^S$ by an order-preserving diffeomorphism. For a subset $V$ of the boundary, a differential inclusion is *persistent relative to $V$* if the closure of every trajectory is disjoint from the closure of $V$, and *repelled by $V$* if for every open $O_1 \supseteq V$ there is an open $O_2 \subseteq O_1$ with $V \subseteq O_2$ such that every trajectory starting outside $O_1$ never enters $O_2$ (being repelled by $V$ implies being persistent relative to $V$). Projecting away a species (forgetting its coordinate) maps a reaction network to a smaller one, and mass-action differential inclusions transform functorially under these projections. The global attractor conjecture asserts that every complex balanced mass-action system has a globally attracting positive equilibrium in each stoichiometric compatibility class.

**Theorem.**

1. *(Projection argument.)* For a family of differential inclusions on hypercubes closed under projection to faces (a vertexical family), if every member is persistent relative to the union of faces opposite to the origin and repelled by the origin, then every member is persistent relative to the whole boundary. This applies to the mass-action inclusions of confined networks that are integer, chemical, reversible, strongly connected, weakly reversible, endotactic or strongly endotactic (as defined on [Permanence of strongly endotactic networks](../global-attractor-conjecture/permanence-of-strongly-endotactic-networks.md)), and to monotone combinations of these classes. For strongly endotactic networks, persistence is strengthened to permanence on that page.
2. *(Induction on species.)* If, for every confined weakly reversible system with at most $n$ species, the mass-action inclusion is persistent and repelled by the origin, then the global attractor conjecture holds for complex balanced systems with at most $n+1$ species. In particular, the conjecture follows from the statement that the mass-action inclusion of every confined weakly reversible system is repelled by the origin and has bounded trajectories.

## Depends on

- [Complex-balanced concentrations](../../complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)
- [Horn–Jackson: one equilibrium per compatibility class](../../complex-balancing-and-the-deficiency-zero-theore/exists-unique-equilibrium-of-is-complex.md)
- [Weakly reversible reaction network](../../../../Dynamics/smooth-dynamics/is-weakly-reversible.md)
- [Permanence of strongly endotactic networks](../global-attractor-conjecture/permanence-of-strongly-endotactic-networks.md)

## Proof depends on

- [The pseudo-Helmholtz function does not increase along solutions](../../complex-balancing-and-the-deficiency-zero-theore/antitone-on-pseudo-helmholtz.md)
- [Equality in the Horn–Jackson inequality](../../complex-balancing-and-the-deficiency-zero-theore/helmholtz-rate-eq-zero-iff.md)

## Expansion

Near a boundary face of the hypercube where some coordinates are small, the dynamics of the remaining coordinates is approximated by the projected network, which belongs to the same family and lives in a lower-dimensional hypercube. Persistence can therefore be proved by induction on the number of species, with the only genuinely new input at each step being the behaviour near the corners (vertices) of the hypercube. For complex balanced systems, persistence implies global convergence because the pseudo-Helmholtz free energy is a strict Lyapunov function with a unique positive equilibrium per compatibility class, so boundary omega-limit points are the only obstruction.

## Sources

- Manoj Gopalkrishnan, Ezra Miller and Anne Shiu, "A Projection Argument for Differential Inclusions, with Applications to Persistence of Mass-Action Kinetics", Symmetry, Integrability and Geometry: Methods and Applications 9 (2013), 025, <https://doi.org/10.3842/sigma.2013.025>; numbering as in arXiv:1208.0874: Theorem 3.15, Corollaries 3.18 and 5.24, Definition 2.4, Theorems 6.8 and 6.10.
