# Luby's maximal independent set algorithm

Let $G = (V, E)$ be a graph with vertex set $V = \{0, \dots, n-1\}$. The algorithm builds an independent set $I$, starting with $I = \emptyset$ and every vertex remaining, and proceeds in rounds on the remaining graph:

1. every remaining vertex $v$ gets a value $P(v)$;
2. a remaining vertex $v$ joins $I$ if $P(v) < P(w)$ for all remaining neighbors $w$; in particular every remaining isolated vertex joins $I$;
3. the vertices that joined $I$ and all their neighbors are removed, together with their incident edges.

The algorithm stops when no vertex remains. In Luby's algorithm every remaining vertex draws an independent uniformly random value $P(v) \in [0, 1]$. These values are almost surely distinct, and their order is then a uniformly random order of the remaining vertices, which is all the algorithm uses. So here the values of a round are those of a uniformly random permutation $\sigma$ of $V$, the vertex $v$ getting the value $\sigma(v)$, and different rounds use independent permutations. The values of a permutation never tie, so the tie-break below matters only for arbitrary values: for values $P(v) \in \mathbb{N}$, ties are broken by vertex index, so that of two vertices with equal values, the one of smaller index counts as smaller.

1. **Maximal independent set.** For any values $P(v) \in \mathbb{N}$, chosen afresh in each round: once no vertex remains, $I$ is a maximal independent set of $G$ and further rounds change nothing; and no vertex remains after $n$ rounds.
2. **Edges removed.** Let $R$ be any set of remaining vertices and run a round on $R$ with a uniformly random permutation. The expected number of removed edges, the edges of $G$ with both endpoints in $R$ and at least one endpoint removed, is at least half the number of edges of $G$ with both endpoints in $R$.
3. **Rounds.** For every $T \in \mathbb{N}$, some vertex remains after $T + 1$ rounds with probability at most $|E| / 2^T$. In particular, for every $c \in \mathbb{N}$, some vertex remains after $(c + 2) \lceil \log_2 n \rceil + 1$ rounds with probability at most $1/n^c$, where $\lceil \log_2 n \rceil$ is the least $k$ with $n \le 2^k$ (and $1/0^c = \infty$ for $c \ge 1$). So the algorithm terminates in $O(\log n)$ rounds with high probability.

Two adjacent vertices cannot both have the smaller value, so $I$ is independent; a removed vertex is in $I$ or adjacent to a vertex of $I$, so once no vertex remains, $I$ is maximal. A round removes at least the remaining vertex of smallest value, so $n$ rounds suffice.

The key estimate behind part 2 is the following. Write $N(w)$ for the set of neighbors of a vertex $w$ in $R$ and $d(w) = |N(w)|$. For an edge $uv$ with $u, v \in R$, the event that $u$ has the smallest value among $N(u) \cup N(v)$ has probability at least $1/(d(u) + d(v))$. When it happens, $u$ joins $I$ and all $d(v)$ edges at $v$ in $R$ are removed. For a fixed $v$ these events are disjoint over the neighbours $u$ of $v$, since two neighbours cannot both have the smallest value in sets that both contain $N(v)$. So the expected number of pairs $(v, e)$ with $e$ an edge at $v$ removed in this way is at least $\sum_{(u,v)} d(v)/(d(u) + d(v))$, the sum over ordered pairs of adjacent vertices of $R$, which equals the number of edges with both endpoints in $R$, because the two orientations of an edge contribute $1$ together. Each removed edge is counted at most twice, once for each endpoint, so at least half of these edges are removed in expectation.

Part 3 follows because the rounds use independent permutations: by part 2, the expected number of remaining edges at least halves in each round, so after $T$ rounds it is at most $|E|/2^T$, and by Markov's inequality some edge remains with probability at most $|E|/2^T$. A round that starts with no remaining edge removes every remaining vertex. The second bound follows from $|E| \le n^2$ and $2^{(c+2) \lceil \log_2 n \rceil} \ge n^{c+2}$.

## Background

- [The LOCAL model](../distributed-execution-models/the-local-model.md)

## Sources

- G. Miller, *Luby's Algorithm for Maximal Independent Set*, lecture notes for 15-451/651, Carnegie Mellon University, 6 December 2019, <http://www.cs.cmu.edu/afs/cs/academic/class/15451-f19/www/LectureNotes/MISLecture.pdf>: Section 3.2 (Algorithm 2, the randomized parallel algorithm) and Section 3.3 (Theorem 3.1 with Claims 3.2 and 3.3, at least half the edges removed in expectation, and Theorem 3.4, $O(\log n)$ rounds with high probability, which the notes prove with a Chernoff bound instead of the expectation argument above).
- M. Luby, "A simple parallel algorithm for the maximal independent set problem", *SIAM Journal on Computing* 15(4):1036–1053, 1986.
