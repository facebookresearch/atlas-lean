# Chvátal–Szemerédi: random k-CNFs require exponential resolution size

For every $k \ge 3$ and every constant $c > 2^k \ln 2$, a random $k$-CNF formula with $n$ variables and $cn$ clauses is unsatisfiable with high probability, and with high probability every resolution refutation of it has size $2^{\Omega(n)}$ (with the constant in $\Omega$ depending on $k$ and $c$). More precisely, refutation width is $\Omega\bigl(n/c^{1/(k-2)+\varepsilon}\bigr)$ for every $\varepsilon > 0$, so size is $2^{\Omega(n/c^{2/(k-2)+\varepsilon})}$ by the size-width relation.

## Proof sketch

The clause-variable incidence hypergraph of a random formula with constant density is a boundary expander for sets of up to $\Omega(n/c^{1/(k-2)+\varepsilon})$ clauses. Any clause derived in a refutation requires a set of axioms of size in a middle range, whose boundary variables must all occur in the derived clause, giving the width bound; Ben-Sasson-Wigderson converts width into size.

## Depends on

- [Width of a clause](../../propositional-logic/resolution-size-and-width/width.md)

## Proof depends on

- [Ben-Sasson–Impagliazzo–Wigderson: near-optimal separation of tree-like and general resolution](biw-tree-vs-dag.md)
- [Ben-Sasson–Wigderson for general resolution](../../propositional-logic/resolution-size-and-width/refutation-narrow.md)

## Sources

- V. Chvátal, E. Szemerédi, "Many hard examples for resolution", Journal of the ACM 35 (1988) 759-768.
- E. Ben-Sasson, A. Wigderson, "Short proofs are narrow - resolution made simple", Journal of the ACM 48 (2001) 149-169.
