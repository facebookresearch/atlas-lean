# Alekhnovich–Johannsen–Pitassi–Urquhart: exponential separation of regular and general resolution

A resolution refutation is **regular** if along every path in its proof DAG from an axiom to the empty clause, no variable is resolved on more than once. There are explicit unsatisfiable CNF formulas $F_n$ of size $\operatorname{poly}(n)$ that have general resolution refutations of size $\operatorname{poly}(n)$ but every regular resolution refutation has size $2^{n^{\Omega(1)}}$. Later lifting-based constructions (Vinyals-Elffers-Johannsen-Nordström) give simplified separations with improved parameters.

## Proof sketch

Take pebbling formulas of suitable pyramid graphs combined with a stone-type extension in which each vertex is assigned one of many ``stones'': general resolution follows the pebbling order, whereas a regular refutation must commit to each stone variable once along every path, and a bottleneck-counting argument with a random restriction shows that many distinct clauses must appear.

## Depends on

- [Resolution refutation](../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

- [Pebbling formulas have linear-size resolution refutations](pebbling-upper-bound.md)

## Sources

- M. Alekhnovich, J. Johannsen, T. Pitassi, A. Urquhart, "An exponential separation between regular and general resolution", Theory of Computing 3 (2007) 81-102; STOC (2002).
- M. Vinyals, J. Elffers, J. Johannsen, J. Nordström, "Simplified and improved separations between regular and general resolution by lifting", SAT (2020).
