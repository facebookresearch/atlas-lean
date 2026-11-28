# Connectivity and diameter of network tiers under head moves

**Setting.** A *binary phylogenetic network* on a leaf set $X$ with $|X|=n\ge 2$ is a directed acyclic graph with one root (indegree $0$, outdegree $1$), $n$ leaves (indegree $1$, outdegree $0$) bijectively labelled by $X$, and all other nodes either split nodes (indegree $1$, outdegree $2$) or reticulations (indegree $2$, outdegree $1$). *Tier-$k$* is the set of such networks with exactly $k$ reticulations.

A *head move* of an edge $e=(u,v)$ to an edge $f$ deletes $e$, subdivides $f$ with a new node $v'$, suppresses the now indegree-1 outdegree-1 node $v$, and adds $(u,v')$; it is allowed only if the result is again a binary phylogenetic network. It is a *distance-$d$ head move* if, after the subdivision, the undirected distance from $v$ to $v'$ is at most $d+1$. Head moves preserve the number of reticulations, so they act within each tier.

**Theorem (connectivity).** For every $k>0$, tier-$k$ is connected by head moves. Moreover it is already connected by distance-2 head moves, whereas distance-1 head moves do not suffice in general.

**Theorem (diameter).** For every $k>0$ and any two tier-$k$ networks $N,N'$ on the same $n$ labels, there is a sequence of at most

$$6n+6k-4$$

head moves turning $N$ into $N'$. Hence the head-move diameter $\Delta_k^{\mathrm{Head}}(n)$ of tier-$k$ is $O(n+k)$.

Tier-$0$ (trees) admits no head moves at all, which is why $k>0$ is required.

## Expansion

The connectivity proof first uses head moves to push all $k$ reticulations to the top of the network, just below the root, arranged as a ladder of $k$ edges $(a_i,b_i)$; at most $k$ further moves redirect them "neatly" in one direction. Below the top the network is a tree, and a reticulation at the bottom of a triangle can be slid along that tree; moving the base triangle simulates rSPR moves of the embedded tree, so any two neatly-topped networks are connected. For the diameter bound, both networks are first brought to a common unlabelled shape using at most $4n+6k-4$ moves in total, and two unlabelled-isomorphic tier-$k$ networks differ by at most $2n$ head moves (a relabelling cost). The distance-2 refinement replaces every step of this argument by local moves, which keeps neighbourhoods small for local-search heuristics.

## Sources

- Remie Janssen, "Heading in the right direction? Using head moves to traverse phylogenetic network space", arXiv:1810.09795: Definitions 5 and 9–10; Theorem 1 (connectivity), Section 4.1 and Theorem 2 (distance-2 head moves), Lemmas 29–30 and Theorem 5 (diameter bound). <https://doi.org/10.48550/arXiv.1810.09795> Published version: Journal of Graph Algorithms and Applications 25 (2021) 263–310, <https://doi.org/10.7155/jgaa.00559>.
