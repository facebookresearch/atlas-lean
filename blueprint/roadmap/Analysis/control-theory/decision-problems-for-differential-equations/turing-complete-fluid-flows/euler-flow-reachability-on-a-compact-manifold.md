# Reachability for the Euler flow on some compact Riemannian manifold is undecidable

There is a constructible compact Riemannian manifold on which the time-dependent incompressible Euler equations simulate every Turing machine; consequently it is undecidable whether the Euler evolution of an explicit initial datum enters an explicit open set of divergence-free fields.

**Theorem (Cardona, Miranda and Peralta-Salas).** There exists a constructible compact Riemannian manifold $(M, g)$ such that the [Euler equations on $(M, g)$ are Turing complete](turing-complete-euler-equations.md). In particular, the problem of determining whether the solution of the Euler equations with an (explicitly constructible) initial datum $X_0 \in \mathfrak X^\infty_{\mathrm{vol}}(M)$ reaches a given (constructible) open set $U \subseteq \mathfrak X^\infty_{\mathrm{vol}}(M)$ is undecidable.

The manifold $M$ is diffeomorphic to $SO(N) \times \mathbb T^N$ for some large $N$, the metric $g$ is constructible but complicated, and $\dim M$ can be bounded by about $10^{35}$. The manifold is fixed; the initial datum and the open set vary with the Turing machine, its input and the prescribed output.

## Depends on

- [Turing complete Euler equations](turing-complete-euler-equations.md)
- [Smooth vector fields](../../../../Geometry/complex-and-symplectic-geometry/weinstein-conjecture/smooth-vector-field.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

The proof first builds a Turing complete polynomial vector field on $\mathbb R^n$, from the simulation of the transition function of a Turing machine by non-autonomous polynomial ODEs (Graça, Campagnolo and Buescu), and from it a Turing complete polynomial vector field $Y$ of degree $58$ on $\mathbb S^{17}$ (Section 4 of the source). Torres de Lizaur's embedding theorem realizes the flow of any polynomial vector field on a sphere as the Euler flow on an invariant submanifold $\Phi(\mathbb S^{17})$ of $\mathfrak X^\infty_{\mathrm{vol}}(M)$ for a constructible compact Riemannian manifold $(M, g)$. The trajectory of $Y$ through $p$ meets $U_{t^*}$ iff the Euler solution with initial datum $\Phi(p)$ meets an open neighborhood $V_{t^*}$ of $\Phi(U_{t^*})$ with $V_{t^*} \cap \Phi(\mathbb S^{17}) = \Phi(U_{t^*})$, so the Euler equations inherit Turing completeness, and the undecidability of the halting problem gives the undecidable reachability. A variation of the construction gives a Turing complete analytic diffeomorphism of $\mathbb S^{17}$, a counterexample to a conjecture of Moore (Theorem 1.3 of the source).

## Sources

- Robert Cardona, Eva Miranda and Daniel Peralta-Salas, "Turing universality of the incompressible Euler equations and a conjecture of Moore", *International Mathematics Research Notices* 2022(22), 2022, pp. 18092–18109, <https://doi.org/10.1093/imrn/rnab233>; read as arXiv:2104.04356v1, <https://arxiv.org/abs/2104.04356v1>: Theorem 1.1 of that version and Remark 1.2 following it, its proof in Section 5 (with the embedding theorem quoted there as Theorem 1.3 of Torres de Lizaur's paper), Sections 3 and 4 (the Turing complete polynomial vector fields, Corollary 3.3 and Theorem 4.1) and Theorem 1.3.
