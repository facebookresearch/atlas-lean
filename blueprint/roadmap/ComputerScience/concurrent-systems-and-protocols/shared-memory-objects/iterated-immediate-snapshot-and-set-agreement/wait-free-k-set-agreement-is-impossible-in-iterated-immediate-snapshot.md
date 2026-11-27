# Wait-free k-set agreement is impossible in iterated immediate snapshot

For $k \ge 1$ and $k + 1$ processes with distinct inputs, no deterministic $R$-round iterated immediate snapshot protocol solves $k$-set agreement (validity: outputs are inputs of participating processes; agreement: at most $k$ distinct outputs). The proof is combinatorial: in the subdivided simplex of IIS executions, any output map satisfying validity is a Sperner colouring, and the number of panchromatic executions (all $k + 1$ values decided) is odd, hence nonzero. In contrast, $t$-resilient $k$-set agreement is solvable whenever $t < k$.

## Proof sketch

Pair up executions differing in whether a boundary process's final singleton block is split or merged; this involution matches non-panchromatic boundary facets except on the faces where one process is missing, and induction on dimension with the Sperner parity argument shows the panchromatic count is odd.

## Depends on

- [Immediate snapshot schedules and iterated immediate snapshot executions](immediate-snapshot-schedules-and-iterated-immediate-snapshot-executions.md)
- [k-set agreement](../../consensus-and-agreement/k-set-agreement.md)

## Proof depends on

- [Borowsky–Gafni characterization of immediate snapshot views](borowsky-gafni-characterization-of-immediate-snapshot-views.md)
- [Sperner's lemma in dimension two (parity form)](../../../../Combinatorics/polytopes-simplicial-complexes/sperner-s-lemma/odd-card-rainbow.md)

## Sources

- Maurice Herlihy and Nir Shavit, "The Topological Structure of Asynchronous Computability", Journal of the ACM, 1999.
- Elizabeth Borowsky and Eli Gafni, "Generalized FLP Impossibility Result for t-Resilient Asynchronous Computations", Proceedings of the Twenty-Fifth Annual ACM Symposium on Theory of Computing (STOC), 1993.
- Michael Saks and Fotios Zaharoglou, "Wait-Free k-Set Agreement Is Impossible: The Topology of Public Knowledge", SIAM Journal on Computing, 2000.
- Elizabeth Borowsky and Eli Gafni, "A Simple Algorithmically Reasoned Characterization of Wait-Free Computations", Proceedings of the Sixteenth Annual ACM Symposium on Principles of Distributed Computing (PODC), 1997.
