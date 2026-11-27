# Resolution lower bound for clique–coloring formulas

If $\mathrm{Clique}_{n,\omega} \wedge \mathrm{Color}_{n,\xi}$ ($\xi < \omega$) has a resolution refutation with $k$ clauses, then the graphs with an $\omega$-clique are separated from the $\xi$-colorable graphs by a monotone circuit of size $k\, n^{O(1)}$. Since for $3 \le \xi < \omega$ with $\sqrt{\xi}\,\omega \le n/(8 \log n)$ every such monotone circuit has size $2^{\Omega(\sqrt{\xi})}$ (Alon–Boppana), taking $\xi = \lceil \sqrt{n} \rceil$ and $\omega = \xi + 1$ shows that for all sufficiently large $n$ every resolution refutation has at least $2^{\Omega(n^{1/4})}$ clauses.

## Proof sketch

The shared edge variables occur only positively in the clique part, so monotone feasible interpolation turns a refutation into a small monotone interpolant, which separates the two graph classes. Razborov's method of approximations as sharpened by Alon and Boppana, which tests circuits only on $\omega$-cliques and complete $\xi$-partite graphs, bounds such circuits from below.

## Depends on

- [Clique–coloring formulas](clique-coloring-formulas.md)
- [Monotone circuits](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/is-monotone-circuit.md)

## Proof depends on

- [Feasible interpolation for resolution](feasible-interpolation-for-resolution.md)
- [Interpolants of clique–coloring formulas are clique–coloring separators](clique-coloring-interpolants-are-separators.md)
- [Razborov: monotone circuits for clique need superpolynomial size](../../../TheoryOfComputation/circuit-complexity/monotone-circuit-lower-bound-for-clique/razborov-monotone-clique.md)
- [Alon–Boppana: monotone circuits for clique need exponential size](../../../TheoryOfComputation/circuit-complexity/monotone-circuit-lower-bound-for-clique/alon-boppana-monotone-clique.md)

## Sources

- J. Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", The Journal of Symbolic Logic 62(2), 457–486, 1997: Theorem 7.2 and Corollary 7.3(1).
- P. Pudlák, "Lower Bounds for Resolution and Cutting Plane Proofs and Monotone Computations", The Journal of Symbolic Logic 62(3), 981–998, 1997: Theorem 2 and Section 5.
- A. A. Razborov, "Lower Bounds on the Monotone Complexity of Some Boolean Functions", Soviet Mathematics Doklady 31, 354–357, 1985.
- N. Alon and R. B. Boppana, "The Monotone Circuit Complexity of Boolean Functions", Combinatorica 7(1), 1–22, 1987.
