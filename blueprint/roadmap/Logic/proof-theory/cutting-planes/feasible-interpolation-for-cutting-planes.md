# Feasible interpolation for cutting planes

Let $\Gamma_A(x, y) \cup \Gamma_B(x, z)$ be an unsatisfiable system of integer linear inequalities with $n$ shared variables $x$ and $N$ variables in total. If it has a cutting planes refutation with $k$ lines whose coefficients are bounded by $M$ in absolute value, then it has an interpolant computed by a Boolean circuit with $k \cdot (MN)^{O(1)} \cdot (Mn)^{O(\log n)}$ gates (Krajíček). If the shared variables occur with nonnegative coefficients in $\Gamma_A$, there is a monotone real circuit of size polynomial in $k$ computing an interpolant (Pudlák), which yields exponential cutting planes lower bounds for clique–coloring formulas.

## Proof sketch

Each line has small communication complexity when its coefficients are small (the players exchange partial sums), so Krajíček's theorem for semantic refutations applies; Pudlák replaces the protocol by a real-gate circuit following the refutation line by line.

## Depends on

- [The cutting planes proof system](cutting-planes-proof-system.md)
- [Interpolants of split CNF formulas](../feasible-interpolation/interpolants-of-split-cnf-formulas.md)

## Proof depends on

- [Krajíček's interpolation theorem for semantic derivations](../feasible-interpolation/krajicek-semantic-interpolation.md)

## Sources

- J. Krajíček, "Interpolation Theorems, Lower Bounds for Proof Systems, and Independence Results for Bounded Arithmetic", The Journal of Symbolic Logic 62(2), 457–486, 1997.
- P. Pudlák, "Lower Bounds for Resolution and Cutting Plane Proofs and Monotone Computations", The Journal of Symbolic Logic 62(3), 981–998, 1997.
