# Effective resistance and electrical networks

A weighted multigraph read as a resistor network with conductances $w$: potentials, the energy $x^{\mathsf T} L x$, effective conductance and effective resistance (D. A. Spielman, *Spectral and Algebraic Graph Theory*, Chapters 11 and 12). Effective resistances drive the sampling sparsifiers of Spielman and Srivastava, where an edge is kept with probability proportional to $w_e R_{\mathrm{eff}}(e)$.

In the probabilistic treatment of R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Chapter 2, the same quantities are organised around energy. Effective conductance is a minimum energy over potentials (Dirichlet's principle, Exercise 2.13), effective resistance is a minimum energy over unit flows (Thomson's principle, Section 2.4), and Rayleigh's monotonicity law follows from either; the Nash-Williams inequality (2.13) bounds effective resistance from below by disjoint cutsets. The network random walk enters through the commute-time identity (Corollary 2.21), and uniform spanning trees through Kirchhoff's effective resistance formula (Section 4.2). Effective conductance is defined below by the Dirichlet minimum; Lyons and Peres define it through escape probabilities, (2.4).

## Energy, effective conductance and effective resistance

- [Effective conductance](effective-conductance.md)
- [Effective resistance](effective-resistance.md)
- [Effective conductance is nonnegative](effective-conductance-nonneg.md)
- [Every admissible potential bounds the effective conductance](effective-conductance-le-energy.md)
- [Dirichlet's principle](is-least-dirichlet-energy.md)
- [Effective resistance is a potential difference](effective-resistance-eq-sub-of-laplacian.md)
- [Range of the weighted Laplacian](range-of-the-weighted-laplacian.md)
- [Rayleigh's monotonicity law](effective-conductance-mono.md)
- [Rayleigh's monotonicity law for effective resistance](effective-resistance-anti.md)

## Thomson's principle

- [Energy of an edge function](flow-energy.md)
- [Energy is nonnegative](flow-energy-nonneg.md)
- [Unit flow](is-unit-flow.md)
- [Current of a potential](current-of.md)
- [The current of a solution of $L v = \delta_s - \delta_t$ is a unit flow](is-unit-flow-current-of.md)
- [Thomson's principle, Pythagorean form](flow-energy-eq-add-flow-energy-sub.md)
- [Thomson's principle](effective-resistance-le-flow-energy.md)
- [Thomson's principle, equality case](flow-energy-eq-effective-resistance-iff.md)
- [Effective resistance as minimum energy (Thomson's principle)](is-least-flow-energy.md)

## The Nash-Williams inequality

- [Separating edge set (cutset)](separating-edge-set.md)
- [A unit flow crosses every cutset](unit-flow-crosses-every-cutset.md)
- [The Nash-Williams inequality](nash-williams-inequality.md)

## Foster's identity and spanning trees

- [Foster's identity](sum-mul-effective-resistance.md)
- [Kirchhoff's effective resistance formula](kirchhoff-effective-resistance-formula.md)
- [Kirchhoff's effective resistance formula, weighted](kirchhoff-effective-resistance-formula-weighted.md)
- [Weighted matrix-tree theorem](weighted-matrix-tree.md)

## Random walks and the commute-time identity

- [The Laplacian of a multigraph applied to a potential](laplacian-mul-vec-apply.md)
- [Neighbour sum of the network walk](neighbour-sum.md)
- [First-step equations for hitting times](is-hitting-time-solution.md)
- [Existence of hitting times](exists-is-hitting-time-solution.md)
- [Uniqueness of hitting times](is-hitting-time-solution-unique.md)
- [Sum of the weighted degrees](sum-weighted-degree.md)
- [Hitting-time identity](hitting-time-identity.md)
- [Commute-time identity](commute-time-identity.md)
- [Commute-time identity for unit conductances](commute-time-identity-one.md)

## Related topics

- [Graph Laplacians and Cheeger's inequality](../graph-laplacians-and-cheeger-s-inequality/README.md): the Laplacian whose quadratic form is the network energy.
- [Spectral sparsification](../../part-02/spectral-sparsification/README.md): Spielman and Srivastava sample edges in proportion to $w_e R_{\mathrm{eff}}(e)$.
- [Kirchhoff's matrix-tree theorem](../kirchhoff-s-matrix-tree-theorem/README.md): for a spanning tree drawn with probability proportional to the product of its edge weights, $w_e R_{\mathrm{eff}}(e)$ is the probability that it contains $e$ (Spielman, *Spectral and Algebraic Graph Theory*, Theorem 13.5.1).
- [Conjugate gradient method](../../../../LinearAlgebra/matrix-decompositions/conjugate-gradient-method/README.md): electrical potentials solve Laplacian systems $Lv = b$, the systems that fast Laplacian solvers attack with preconditioned iterative methods.
- [Conductance and Cheeger's inequality](../../part-02/conductance-and-cheeger-s-inequality/README.md): the weighted degree used by the network random walk is defined there.
- [Dirichlet forms](../../../../Probability/markov-chains/dirichlet-forms/README.md): the network energy $\sum_e w_e (x(e_1) - x(e_2))^2$ is the Dirichlet form of the network random walk, with $\pi(x) P(x, y)$ the conductance of $xy$.
- [Canonical paths and multicommodity flow](../../../../Probability/markov-chains/canonical-paths-and-multicommodity-flow/README.md): Sinclair's flows in the network of a reversible chain, the multicommodity counterpart of the unit flows of Thomson's principle.
- [Random walks on finite groups](../../../../Probability/random-walks/random-walks-on-finite-groups/README.md): Diaconis's random walks; on a Cayley graph the network random walk with unit conductances is simple random walk on the group.
- [Max-flow min-cut theorem](../../../matchings-and-flows/max-flow-min-cut-theorem/README.md): flows with capacity constraints, as opposed to the energy-minimising flows here.
