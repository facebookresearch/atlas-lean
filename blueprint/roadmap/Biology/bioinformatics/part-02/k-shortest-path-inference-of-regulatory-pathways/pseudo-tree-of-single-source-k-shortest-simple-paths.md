# Pseudo tree of single-source $k$-shortest simple paths

**Setting.** $G = (V, E)$ is a directed graph with $n$ nodes, $m$ edges and nonnegative edge lengths $d$ (for gene networks, e.g. $-\log$ of interaction confidence), with source gene $S$. For each node $A \ne S$, the *top-$k$ shortest paths* are the $k$ shortest simple paths from $S$ to $A$.

**Definitions.** A **pseudo tree** stores all top-$k$ shortest paths from $S$ to every node as root-to-node paths (**tree-paths**) of a rooted tree, obtained from the shortest-path tree ($k = 1$) by merging the 2nd to $k$-th shortest paths into it along their longest common prefixes. A tree node is a **path node** if its tree-path is a top-$k$ shortest path to its graph node, and a **dummy node** otherwise (a prefix of a top-$k$ path to a farther node need not itself be top-$k$).

**Theorem.**
1. *(Dummy-node structure.)* If a top-$k$ shortest path $P$ from $S$ to $A$ passes through a dummy node $B$, with suffix $P_{BA}$ from $B$ to $A$, then every top-$k$ shortest path $P_{SB}$ from $S$ to $B$ either meets $P_{BA}$ at a node other than $B$, or is the prefix of some top-$k$ shortest path from $S$ to $A$.
2. *(Size.)* The pseudo tree has exactly $(n-1)k$ path nodes (when $k$ simple paths exist to every node) and $O(n^2 k)$ nodes in total, and this order is attained by some graphs.
3. *(Path-node construction.)* Growing the tree Dijkstra-style, repeatedly adding the cheapest extension $S \Rightarrow N'_a \to N'_b$ that keeps the tree-path simple and gives $N_b$ fewer than $k$ copies, with tree height capped at $h$, runs in $O\big(nk\log(nk) + mk(h + k)\big)$ time with a Fibonacci-heap priority queue, versus $O\big(nhk(m + n\log n)\big)$ for $n - 1$ runs of Yen's single-pair algorithm.

## Expansion

For item 1, write $P = P_1 + P_{BA}$ with $P_1$ not top-$k$ to $B$ (since $B$ is a dummy). If some top-$k$ path $P'_1$ to $B$ avoided $P_{BA}$ except at $B$ and were not a prefix of a top-$k$ path to $A$, then $P'_1 + P_{BA}$ would be a simple path to $A$ shorter than $P$ (because $d(P'_1) < d(P_1)$) yet not top-$k$, so $P$ could not be top-$k$, a contradiction. For item 2, the $n - 1$ path nodes of the shortest-path tree need no dummies, and each of the other $(n-1)(k-1)$ path nodes needs at most $n - 2$ dummy ancestors, giving at most $(n-1)(n-2)(k-1)$ dummies; a chain construction in which every second-to-$k$-th path to $A_i$ must traverse a long chain of $B$ nodes whose own top-$k$ paths all contain the $A$ chain realizes $q(q-1)(k-1)$ dummies with $q = \Theta(n)$. Because dummies are rare in real interaction networks, the heuristic in item 3 keeps only path nodes; each node is enqueued at most $k$ times (at most $nk$ insertions), each edge triggers at most $2k$ key updates, and each expansion costs $O(h)$ to test simplicity and $O(k)$ to maintain the sorted list of current paths. A diversity step then re-ranks near-duplicate paths so that the reported pathways cover different functions.

## Sources

- Y.-K. Shih and S. Parthasarathy, "A single source k-shortest paths algorithm to infer regulatory pathways in a gene network", Bioinformatics 28 (2012), i49–i58, Section 4.2 (Definitions 1–3, Theorems 1–3, Algorithm 1), <https://doi.org/10.1093/bioinformatics/bts212>, PMCID: PMC3371844.
- J. Y. Yen, "Finding the k shortest loopless paths in a network", Management Science 17 (1971), 712–716.
