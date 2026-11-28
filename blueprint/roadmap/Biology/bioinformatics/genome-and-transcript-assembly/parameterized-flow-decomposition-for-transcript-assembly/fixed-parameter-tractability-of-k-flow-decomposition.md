# Fixed-parameter tractability of $k$-flow decomposition

**Problem.** Let $G$ be a directed acyclic graph with source $s$ and sink $t$ and $f$ an integral $s$–$t$ flow on it (in transcript assembly, nodes are exon segments, arcs are observed splice junctions and $f$ is read coverage). A **flow decomposition** is a family of $s$–$t$ paths $p_1,\dots,p_k$ with positive integer weights $w_1,\dots,w_k$ such that every arc $e$ carries $f(e)=\sum_{i:\,e\in p_i}w_i$; the paths are candidate transcripts and the weights their abundances. **$k$-Flow Decomposition** ($k$-FD) asks whether a decomposition into at most $k$ paths exists; it is NP-hard.

**Theorem.** Let $n=|V(G)|$ and $\lambda$ the logarithm of the largest flow value.
1. $k$-FD is solvable in time $2^{O(k^2)}(n+\lambda)$, i.e. it is fixed-parameter tractable in the number $k$ of paths and linear in the input size; the explicit bound is $4^{k^2}k^{1.5k}k^{o(k)}1.765^k\,(n+\lambda)$.
2. $k$-FD admits no polynomial kernel unless $\mathrm{NP}\subseteq\mathrm{coNP}/\mathrm{poly}$; neither do its variants with weights restricted to a given set $\mathcal{W}\subset\mathbb{Z}$.
3. Even with the $k$ paths prescribed, assigning integral weights to them so as to obtain a flow decomposition ($k$-Flow Weight Assignment) is NP-complete, by reduction from Exact 3-Hitting Set.

## Expansion

The algorithm is a dynamic program over a topological ordering $v_1,\dots,v_n$: for each prefix $S_i$ it enumerates the routings of the $k$ unknown paths over the cut of arcs leaving $S_i$, of which there are at most $\sqrt{k}\,(0.649k)^k$, each extending a routing of the previous cut. The weights are not guessed: each candidate routing yields a system of linear equations "flow on arc $e$ equals the sum of the weights of the paths through $e$", and the equations collected along the scan are solved over the integers with Lenstra-type integer programming in dimension $k$, which is FPT in $k$ (time $O(k^{2.5k+o(k)}|L|)$). Table entries whose linear system has no solution can be discarded, and the kernel lower bound comes from an AND-cross-composition of an NP-hard problem.

## Sources

- Kyle Kloster, Philipp Kuinke, Michael P. O'Brien, Felix Reidl, Fernando Sánchez Villaamil, Blair D. Sullivan and Andrew van der Poel, "A practical fpt algorithm for Flow Decomposition and transcript assembly", arXiv:1706.07851 (2017), problem definitions, the routing-count lemma, the running-time theorem for the dynamic program, the NP-completeness theorem for weight assignment and the no-polynomial-kernel theorem, <https://doi.org/10.48550/arXiv.1706.07851>.
