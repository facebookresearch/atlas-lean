# Minimum cycle mean

The minimum, over the directed cycles of a weighted digraph, of the average edge weight. Karp (1978) characterised it through the minimum weights $F_k(v)$ of walks with exactly $k$ edges from a fixed vertex, which the Bellman–Ford recurrence computes, giving an $O(n|E|)$ algorithm; a negative cycle exists exactly when the minimum cycle mean is negative.

- [Directed cycle in a weighted edge list](is-directed-cycle.md)
- [Minimum cycle mean of a weighted edge list](is-min-cycle-mean.md)
- [Minimum weight of a walk with $k$ edges](is-min-walk-weight.md)
- [Karp's minimum cycle mean theorem](karp-min-cycle-mean.md)

## Related topics

- [Bellman–Ford algorithm](../bellman-ford-algorithm/README.md): the recurrence $F_k(v) = \min_{(u,v)} (F_{k-1}(u) + w(u,v))$ computing Karp's quantities, and negative-cycle detection.
