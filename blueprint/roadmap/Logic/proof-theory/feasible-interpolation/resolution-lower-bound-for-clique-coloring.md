# Resolution lower bound for clique–coloring formulas

Every resolution refutation of $\mathrm{Clique}_{n,k} \wedge \mathrm{Color}_{n,k-1}$ has more than half as many lines as the least monotone circuit separating $k$-cliques from complete $(k-1)$-partite graphs. Consequently, for $2 \le k$ and $k^4 \le n$ every refutation has more than $2^{2\lfloor\sqrt{k}\rfloor}/2$ lines, and with $k \approx n^{1/4}$ the size is $2^{\Omega(n^{1/8})}$; via Alon–Boppana approximators, suitable parameters give $2^{n^{\Omega(1)}}$ lower bounds.

## Proof sketch

Monotone feasible interpolation turns a refutation with $s$ lines into a monotone circuit with at most $2s$ gates computing a separator; Razborov's method of approximations, which reads circuits only on $k$-cliques and complete $(k-1)$-partite graphs, bounds such circuits from below.

## Depends on

- [Clique–coloring formulas](clique-coloring-formulas.md)

## Proof depends on

- [Feasible interpolation for resolution](feasible-interpolation-for-resolution.md)
- [Interpolants of clique–coloring formulas are clique–coloring separators](clique-coloring-interpolants-are-separators.md)
- [Razborov: monotone circuits for clique need superpolynomial size](../../../TheoryOfComputation/circuit-complexity/monotone-circuit-lower-bound-for-clique/razborov-monotone-clique.md)
- [Alon–Boppana: monotone circuits for clique need exponential size](../../../TheoryOfComputation/circuit-complexity/monotone-circuit-lower-bound-for-clique/alon-boppana-monotone-clique.md)

## Sources

- J. Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", The Journal of Symbolic Logic 62(2), 457–486, 1997.
- P. Pudlák, "Lower Bounds for Resolution and Cutting Plane Proofs and Monotone Computations", The Journal of Symbolic Logic 62(3), 981–998, 1997.
- A. A. Razborov, "Lower Bounds on the Monotone Complexity of Some Boolean Functions", Soviet Mathematics Doklady 31, 354–357, 1985.
- N. Alon and R. B. Boppana, "The Monotone Circuit Complexity of Boolean Functions", Combinatorica 7(1), 1–22, 1987.
