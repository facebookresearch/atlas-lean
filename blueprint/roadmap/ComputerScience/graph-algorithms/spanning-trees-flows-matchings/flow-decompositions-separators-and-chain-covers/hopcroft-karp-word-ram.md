# Hopcroft-Karp in O((m + r + |E|) sqrt(nu)) word-RAM time

There is a deterministic word-RAM program that, given a bipartite graph with $m$ left vertices, $r$ right vertices and edge set $E$ in compressed sparse row form, computes a maximum matching and a minimum vertex cover of equal size in $O\big((m + r + |E|)\sqrt{\nu + 1}\,\big)$ instructions, where $\nu$ is the maximum matching size; hence $O\big((m + r + |E|)\sqrt{\min(m, r) + 1}\big)$. For a dense $0/1$ matrix input the bound is $O\big((m + r)^2 \sqrt{\nu + 1}\big)$.

## Proof sketch

Each phase is one breadth-first layering and one iterative depth-first augmentation pass in linear time, and there are at most $2\lfloor \sqrt{\nu} \rfloor$ augmenting phases by the Hopcroft-Karp phase bound, plus one final search that finds no augmenting path.

## Depends on

- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)
- [Compressed-sparse-row encoding of a directed graph](../../../sorting-and-searching/word-ram-integer-algorithms/compressed-sparse-row-graph-encoding.md)

## Proof depends on

- [Hopcroft and Karp's bound on the number of phases](../maximum-bipartite-matching/card-le-hopcroft-karp-aux-sqrt.md)

## Sources

- J. E. Hopcroft and R. M. Karp, "An n^{5/2} Algorithm for Maximum Matchings in Bipartite Graphs", SIAM Journal on Computing 2(4), 1973.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
