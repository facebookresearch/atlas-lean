# Minimum walk cover of a bidirected graph by imbalance

**Setting.** A *bidirected graph* (bigraph) $G = (V, E, c)$ has arcs whose two ends each attach to a node with an orientation ($\oplus$ forward or $\ominus$ reverse), modeling DNA strands; $c$ maps a node to its reverse complement. For a node $v$ that is not self-complemental, its outdegree $\delta^+(v)$ and indegree $\delta^-(v)$ count arc ends leaving $v^{\oplus}$ and $v^{\ominus}$, and $\mathrm{imbalance}(v) = \delta^+(v) - \delta^-(v)$; for a self-complemental node, $\mathrm{imbalance}(v) = 1$ if its degree is odd and $0$ otherwise. The imbalance of the graph is $\mathrm{imbalance}(G) = \sum_{v} |\mathrm{imbalance}(v)|$. A *unique walk cover* is a set of walks using every arc exactly once (in either direction).

**Results.**

1. $\mathrm{imbalance}(G)$ is even.
2. In any unique walk cover, at least $|\mathrm{imbalance}(v)|$ walks start at $v$, or at least that many end at $v$.
3. Every unique walk cover of $G$ has at least $\mathrm{imbalance}(G)/2$ walks.
4. A connected bigraph can be made Eulerian (all imbalances zero) by inserting arcs between unbalanced nodes in $O(|V| + |E|)$ time, and a Eulerian cycle of a connected Eulerian bigraph can be found in $O(|V| + |E|)$ time. Breaking the cycle at the inserted arcs gives a walk cover with $\max\bigl(1, \mathrm{imbalance}(G)/2\bigr)$ walks, which is minimum.

## Expansion

Adding or removing an arc changes the imbalance of two nodes by one or of one node by two, so parity is preserved from the empty graph. A walk passing through $v$ uses one in-end and one out-end, so surplus arc ends at an unbalanced node must be absorbed by walk endpoints; each walk has two endpoints, giving the bound. This is the bidirected analogue of the classical fact that a connected directed graph decomposes into $\max(1, \sum_v |\delta^+(v) - \delta^-(v)|/2)$ trails.

## Sources

- S. Schmidt and J. N. Alanko, "Eulertigs: minimum plain text representation of k-mer sets without repetitions in linear time", *Algorithms for Molecular Biology* (2023), Preliminaries (bidirected graphs, imbalance), Lemma 9, Definition 10, Theorem 11, Lemma 13 and Theorems 16 and 19. <https://doi.org/10.1186/s13015-023-00227-1> (PMC10318842)
