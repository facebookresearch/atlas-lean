# Local and global PageRank centralities of multilayer networks

Consider a multi-tissue gene network as a multilayer network with $L$ layers (tissues) on a common set of $n$ genes, so $N = nL$ gene-tissue nodes. Its $N \times N$ supra-adjacency matrix splits as $M = A + C$, where $A = \mathrm{diag}(A^{[1,1]}, \dots, A^{[L,L]})$ holds the within-layer edges and $C$ (zero diagonal blocks) the between-layer edges. Assume $A, C \ge 0$ entrywise and that $M$ is normalized so that its spectral radius satisfies $\rho(M) \le 1$ (for instance $M$ stochastic). Fix $p \in [0, 1)$, let $\mathbf{1}$ be the all-ones vector, $\mathbf{1}^{[i]}$ its restriction to layer $i$, and $A^{[i]}$ the matrix $A$ with all column blocks except block $i$ set to zero. Define:

- **Versatility** (multilayer PageRank): $x = pMx + \frac{1-p}{N}\mathbf{1}$.
- **Local centrality**: $l = pAl + \frac{1-p}{n}\mathbf{1}$, and per layer $l_i = pA^{[i]} l_i + \frac{1-p}{n}\mathbf{1}^{[i]}$.
- **Global centrality**: $g = p\big[(A + C)g + Cl\big] + \frac{1-p}{N}\mathbf{1}$.
- **Layer-specific centrality** for target layer $i$: $g_i = p\big[(A+C)g_i + Cl_i\big] + \frac{1-p}{N}\mathbf{1}^{[i]}$.
- **Local-set** and **query-set centralities** for a set $Q_k$ of query genes in layer $i$: the same two equations with $\mathbf{1}^{[i]}$ replaced by the indicator $\mathbf{1}_{Q_k}$ (and $l_i$ by the local-set vector in the query-set equation).

**Theorem (convergence).** For $0 \le p < 1$ each of these fixed-point equations has a unique solution, and the iteration $y \mapsto pBy + c$ defining it converges to that solution from any starting vector.

## Expansion

Each equation has the form $y = pBy + c$ with $B \in \{A, A^{[i]}, M\}$ and a constant vector $c$ (for global-type centralities $c$ contains $pCl$, already determined). Since $0 \le A^{[i]} \le A \le M$ entrywise, Perron-Frobenius monotonicity gives $\rho(pB) \le p\,\rho(M) < 1$. Unrolling the iteration $k$ times gives $y = (pB)^k y + \sum_{j<k} (pB)^j c$, the first term vanishes and the Neumann series converges, so $y = (I - pB)^{-1} c$ is the unique solution. Interpretation: local centrality is a random walk with restart confined to one tissue; global centrality adds steps across tissues weighted by the local centrality of the arrival node, so a gene scores highly if it reaches, within or across tissues, genes that are themselves locally central; query-set centrality ranks genes by their multi-hop influence on a chosen gene set (for example hormone-responsive genes) in a target tissue.

## Sources

- T. Kumar, R. Sethuraman, S. Mitra, B. Ravindran, M. Narayanan, "MultiCens: Multilayer network centrality measures to uncover molecular mediators of tissue-tissue communication", PLoS Computational Biology (2023), Methods: Eqs. 1-10 (supra-adjacency decomposition, versatility, local, global, layer-specific, local-set and query-set centralities), Lemmas 1-4 and Theorem 1 (convergence), Lemmas 5-8 and Theorem 2 (decomposability, Eqs. 11-14). <https://doi.org/10.1371/journal.pcbi.1011022> (PMC10159362)
