# Luby's maximal independent set algorithm

Let $G = (V, E)$ be a graph with $n$ vertices. The randomized algorithm proceeds in rounds on the remaining graph:

1. every remaining isolated vertex joins the independent set $I$;
2. every remaining vertex $v$ draws an independent uniformly random value $P(v) \in [0, 1]$;
3. a vertex joins $I$ if $P(v) < P(w)$ for all remaining neighbors $w$;
4. the vertices that joined $I$ and all their neighbors are removed, together with their incident edges.

The output is a maximal independent set of $G$. Two adjacent vertices cannot both have the smaller value, so $I$ is independent; and the algorithm stops only when every vertex is in $I$ or adjacent to it.

1. **Edges removed.** In each round the expected number of removed edges is at least half the number of remaining edges.
2. **Rounds.** The algorithm terminates in $O(\log n)$ rounds with high probability.

The key estimate behind part 1 is the following. For an edge $uv$, the event that $u$ has the smallest value among $N(u) \cup N(v)$ has probability at least $1/(d(u) + d(v))$. When it happens, $u$ joins $I$ and all $d(v)$ edges at $v$ are removed. For a fixed $v$ these events are disjoint over the neighbours $u$ of $v$, since two neighbours cannot both have the smallest value in sets that both contain $N(v)$. So the expected number of pairs $(v, e)$ with $e$ an edge at $v$ removed in this way is at least $\sum_{(u,v)} d(v)/(d(u) + d(v))$, the sum over ordered edges, which equals $|E|$ because the two orientations of an edge contribute $1$ together. Each removed edge is counted at most twice, once for each endpoint, so at least $|E|/2$ edges are removed in expectation. Part 2 follows because the rounds use independent random values, so the number of edges shrinks geometrically in expectation. In the LOCAL model each round takes $O(1)$ communication rounds, so the algorithm computes a maximal independent set in $O(\log n)$ rounds with high probability.

## Proof depends on

- [Luby's selection step yields an independent set](../../parallel-algorithms/luby-s-maximal-independent-set-algorithm/luby-select-is-indep-set.md)

## Background

- [The LOCAL model](../distributed-execution-models/the-local-model.md)

## Sources

- G. Miller, *Luby's Algorithm for Maximal Independent Set*, lecture notes for 15-451/651, Carnegie Mellon University, 6 December 2019, <http://www.cs.cmu.edu/afs/cs/academic/class/15451-f19/www/LectureNotes/MISLecture.pdf>: Section 3.2 (Algorithm 2, the randomized parallel algorithm) and Section 3.3 (Theorem 3.1, at least half the edges removed in expectation, and Theorem 3.4, $O(\log n)$ rounds with high probability).
- M. Luby, "A simple parallel algorithm for the maximal independent set problem", *SIAM Journal on Computing* 15(4):1036–1053, 1986.
