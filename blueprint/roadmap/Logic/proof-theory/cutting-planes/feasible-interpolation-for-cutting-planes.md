# Feasible interpolation for cutting planes

Let $\Gamma_A(x, y) \cup \Gamma_B(x, z)$ be an unsatisfiable system of integer linear inequalities with $n$ shared variables $x$ and $N$ variables in total. If it has a cutting planes refutation with $k$ lines whose coefficients are bounded by $M$ in absolute value, then it has an interpolant computed by a Boolean circuit with $k \cdot (MN)^{O(1)} \cdot (Mn)^{O(\log n)}$ gates (Krajíček). Under the same coefficient bound, if the shared variables occur only with nonnegative coefficients in $\Gamma_A$ (or only with nonpositive ones in $\Gamma_B$), the same bound holds for a monotone Boolean interpolant (Krajíček). Without any bound on the coefficients, there is an interpolating circuit of size polynomial in $k$ and in the binary length of the constant terms of the initial inequalities, and in the monotone case a monotone real circuit of size linear in $N$ and $k$ computing an interpolant (Pudlák). With the exponential lower bound for monotone real circuits separating cliques from complete multipartite graphs, this yields exponential cutting planes lower bounds for clique–coloring formulas.

## Proof sketch

Each line has small communication complexity when its coefficients are small (the players exchange the partial sums over their own variables, and find a differing shared coordinate by binary search), so Krajíček's theorem for semantic refutations applies. Pudlák instead evaluates the refutation line by line, computing for each line the value of its shared-variable part with gates for addition and rounded division, which are monotone real gates in the monotone case.

## Depends on

- [The cutting planes proof system](cutting-planes-proof-system.md)
- [Interpolants of split CNF formulas](../feasible-interpolation/interpolants-of-split-cnf-formulas.md)
- [Monotone real circuits](../stabbing-planes-and-semi-algebraic-branching/monotone-real-circuit.md)

## Proof depends on

- [Krajíček's interpolation theorem for semantic derivations](../feasible-interpolation/krajicek-semantic-interpolation.md)
- [Clique–coloring formulas](../feasible-interpolation/clique-coloring-formulas.md)
- [Haken–Cook / Pudlák: exponential lower bounds for monotone real circuits](../stabbing-planes-and-semi-algebraic-branching/haken-cook-monotone-real.md)

## Sources

- J. Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", The Journal of Symbolic Logic 62(2), 457–486, 1997: Theorem 6.4 and Corollary 7.3(2).
- P. Pudlák, "Lower Bounds for Resolution and Cutting Plane Proofs and Monotone Computations", The Journal of Symbolic Logic 62(3), 981–998, 1997: Theorems 3, 4 and 6.
