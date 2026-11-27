# Subcritical Hopf bifurcation in the space-clamped Hodgkin–Huxley equations

For the space-clamped Hodgkin–Huxley equations with the [standard squid-axon parameters and a constant applied current $I$](../hodgkin-huxley-equilibria-under-an-applied-curre/squid-i.md), the equilibrium undergoes a Hopf bifurcation at $I \approx 9.78$ (in the units of the model). For these parameters an [equilibrium exists for every applied current](../hodgkin-huxley-equilibria-under-an-applied-curre/exists-equilibrium.md), and the [equilibrium branch first stops being Hurwitz at a spectral Hopf candidate](../hodgkin-huxley-equilibria-under-an-applied-curre/exists-spectral-hopf-candidate.md). Guckenheimer and Oliva (2002, Section 2), recalling the numerical studies of Rinzel and Miller and of Hassard, report that this bifurcation is subcritical: a family of unstable periodic orbits collapses onto the equilibrium at the bifurcation, and, followed by numerical continuation as $I$ decreases, this family passes three saddle-node bifurcations of periodic orbits, the third of which joins it to a family of stable periodic orbits. Hence the model has a range of currents in which a stable rest state coexists with stable repetitive firing. The direction of the bifurcation rests on computation: a statement with explicit error control for these parameter values, such as a validated sign of the first Lyapunov coefficient, is the target of the Expansion.

## Depends on

- [Squid giant axon parameters with applied current I](../hodgkin-huxley-equilibria-under-an-applied-curre/squid-i.md)
- [Existence of an equilibrium for every applied current](../hodgkin-huxley-equilibria-under-an-applied-curre/exists-equilibrium.md)
- [Squid branch first stops being Hurwitz at a spectral Hopf candidate](../hodgkin-huxley-equilibria-under-an-applied-curre/exists-spectral-hopf-candidate.md)

## Expansion

1. The model: the four-dimensional Hodgkin–Huxley system with the standard rate functions and parameters, and the curve of equilibria parametrized by $I$.
2. The Hopf condition: a pair of simple purely imaginary eigenvalues crossing transversally at the bifurcation current, with no other eigenvalue on the imaginary axis.
3. The first Lyapunov coefficient at the bifurcation and a validated (interval-arithmetic) computation of its sign.
4. The branch of unstable periodic orbits, its saddle-node bifurcations and the connection with the stable periodic orbits, as separate statements.
5. The [slow traveling pulse of the Hodgkin–Huxley equations](../../../Biology/pattern-formation/slow-traveling-pulse-of-the-hodgkin-huxley-equations.md) is background only.

## Sources

- J. Guckenheimer and R. A. Oliva, Chaos in the Hodgkin–Huxley model, SIAM J. Appl. Dyn. Syst. 1 (2002), 105–114, Sections 1–2. <https://doi.org/10.1137/s1111111101394040>
- Original result: B. Hassard, Bifurcation of periodic solutions of the Hodgkin–Huxley model for the squid giant axon, J. Theor. Biol. 71 (1978), 401–420. <https://doi.org/10.1016/0022-5193(78)90168-6> The subcriticality of the bifurcation follows Guckenheimer and Oliva (2002, Section 2).
