# Dijkstra's algorithm with a Fibonacci heap in O(m + n log n) word-RAM time

There is a single deterministic word-RAM program that, given a directed graph with $n$ vertices, $m$ arcs, natural-number arc weights in compressed sparse row form and a source $s$, computes the shortest-path distance from $s$ to every vertex (and reports unreachable vertices) within

$$
C\,\big(m + n(\lfloor \log_2 n \rfloor + 1)\big)
$$

instructions for an absolute constant $C$, using a Fibonacci heap as the indexed priority queue, at every word size large enough for the input words and the distances.

## Proof sketch

Combine the operation count of Dijkstra's algorithm with the Fredman-Tarjan amortized bounds: $O(1)$ for insertion and decrease-key and $O(\log n)$ for extract-min; the memory layout realizes the amortized bounds as instruction counts.

## Depends on

- [Dijkstra's algorithm in priority-queue operations](dijkstra-priority-queue-operation-count.md)
- [Decrease-key in a Fibonacci heap](../../../data-structures/heaps/fibonacci-heap/decrease-key.md)
- [Compressed-sparse-row encoding of a directed graph](../../../sorting-and-searching/word-ram-integer-algorithms/compressed-sparse-row-graph-encoding.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Dijkstra's algorithm in priority-queue operations](dijkstra-priority-queue-operation-count.md)

## Sources

- M. L. Fredman and R. E. Tarjan, "Fibonacci Heaps and Their Uses in Improved Network Optimization Algorithms", Journal of the ACM 34(3), 1987.
- E. W. Dijkstra, "A Note on Two Problems in Connexion with Graphs", Numerische Mathematik 1, 1959.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
