# Decomposition of restricted graphs: progress in size or kappa with O(log n) expected hits per shortest path

Let $G$ be a restricted graph with source $s$ and $n$ vertices, $m$ edges, and let $\kappa\ge\kappa(G)$. There is a randomized algorithm $\mathrm{Decompose}(G,\kappa)$ running in expected time $O((m+n\log\log n)\log n)$ that computes $S\subseteq E(G)$ such that

1. (progress) with high probability, every strongly connected component $C$ of $G\setminus S$ satisfies $|C|\le\frac34|V(G)|$ or $\kappa(G[C\cup\{s\}])\le\kappa/2$;
2. (sparse hitting) for every shortest $s$-$v$ path $P$ in $G$, $\mathbb{E}[|P\cap S|]=O(\log n)$.

Consequently, whenever the progress property holds, $|C|\cdot\kappa_C\le\frac34|V|\cdot\kappa$ for the bound $\kappa_C$ passed to the recursive call on each component $C$ of $G\setminus S$ ($\kappa_C=\kappa$ if $|C|\le\frac34|V|$ and $\kappa_C=\kappa/2$ otherwise); starting from $\kappa=n$, a valid bound since $\kappa(G)\le n-1$ for simple paths, the recursion then has depth $O(\log(n\kappa))=O(\log n)$, and Restricted SSSP can be solved in expected time $O((m+n\log\log n)\log^2 n)$, or in that worst-case time with error probability $\frac12$ by stopping after twice the expected time.

## Proof sketch

The procedure classifies vertices as out-light or in-light by whether their out- or in-ball of radius $\kappa/4$ in $G_{\ge 0}$ (negative weights raised to $0$) contains at most $\frac34$ of the vertices, and carves balls in $G_{\ge 0}$ of radius drawn from $\mathrm{Geom}(20\log n/\kappa)$ around light vertices; the memoryless radius gives each edge a cut probability proportional to its rounded weight over the radius, and summing along a shortest path, whose positive part is controlled by $\kappa$ and the cycle-mean bound, yields $O(\log n)$ expected hits. Components left after carving either lose a quarter of the vertices or consist of heavy vertices, where a nonpositive path with more than $\kappa/2$ negative edges would combine with the large balls into a cycle of mean below $1$. Recombining after recursion uses the Dijkstra-Bellman-Ford hybrid with Thorup's priority queue, costing $O((m+n\log\log n))$ per expected hit.

## Depends on

- [Restricted graphs and the parameter kappa counting negative edges on nonpositive paths](restricted-graphs-and-kappa.md)
- [Weak and strong directed low-diameter decompositions with overhead rho](directed-low-diameter-decomposition.md)

## Proof depends on

- [ElimNeg: the Dijkstra-Bellman-Ford hybrid runs in time proportional to the negative-edge counts of shortest paths](elimneg-dijkstra-bellman-ford-hybrid.md)

## Sources

- Karl Bringmann, Alejandro Cassis, Nick Fischer, "Negative-Weight Single-Source Shortest Paths in Near-Linear Time: Now Faster!", FOCS (2023), arXiv:2304.05279.
