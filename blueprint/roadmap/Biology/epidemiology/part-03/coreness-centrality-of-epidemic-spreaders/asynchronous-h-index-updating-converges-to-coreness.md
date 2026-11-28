# Asynchronous H-index updating converges to coreness

**Setting.** Let $G = (V, E)$ be a finite undirected simple graph with degrees $k_j$, and let $\mathcal H$ be the H-operator (the largest $y$ such that at least $y$ arguments are $\ge y$), as in [H-index iteration converges to coreness](h-index-iteration-converges-to-coreness.md). Initialize $g_j = k_j$ for all $j \in V$. At each step choose one node $i$ (for example uniformly at random) and replace

$$g_i \leftarrow \mathcal H\big(g_{j} : j \in N(i)\big),$$

using the current values of the neighbors, which may have been updated any number of times. Assume every node is chosen infinitely often (true almost surely under uniform random choice).

**Theorem.** After finitely many steps the process reaches a state in which no update changes any $g$ value, and in that steady state $g_i = c_i$, the coreness of node $i$, for every $i \in V$.

Because each update uses only the values at a node and its neighbors and no global clock, coreness can be computed by a decentralized algorithm, and previously computed values remain valid starting points when links or nodes are added to an evolving contact network.

## Depends on

- [H-index iteration converges to coreness](h-index-iteration-converges-to-coreness.md)

## Expansion

*Monotonicity.* By induction over update times, each node's successive values are nonincreasing: an update of $i$ applies the monotone operator $\mathcal H$ to neighbor values that are each no larger than at $i$'s previous update. Values are nonnegative integers, so each node changes only finitely often, and since every node is chosen infinitely often the process reaches a fixed point after finitely many steps.

*Never below coreness.* Suppose some node first drops below its coreness, say $g_i < c_i$ after an update at step $t$, while all nodes satisfied $g_j \ge c_j$ before. In the $c_i$-core, $i$ has at least $c_i$ neighbors, each with coreness $\ge c_i$ and hence current value $\ge c_i$, so $\mathcal H$ returns at least $c_i$, a contradiction.

*Not above coreness.* At the fixed point $g_i = \mathcal H(g_j : j \in N(i))$ for every $i$, so, as in the synchronous proof, the nodes with $g_j \ge g_i$ induce a subgraph of minimum degree $\ge g_i$ containing $i$; hence $c_i \ge g_i$.

## Sources

- L. Lü, T. Zhou, Q.-M. Zhang, H. E. Stanley, "The H-index of a network node and its relation to degree and coreness", *Nature Communications* 7 (2016) 10168. Results (Theorem 2, asynchronous updating Eq. (4)); Methods, "Proof of Theorem 2". <https://doi.org/10.1038/ncomms10168>. PMCID: PMC4729922.
