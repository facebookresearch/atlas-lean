# Appendage and structural homeostasis subnetworks

**Setting.** Let $\mathcal{G}$ be a core input-output network with input node $\iota$ and output node $o$ (every node downstream of $\iota$ and upstream of $o$), with homeostasis matrix $H$ and Frobenius-König factorization $\det H=\det B_1\cdots\det B_m$ into irreducible blocks (see [Determinant criterion for infinitesimal homeostasis](determinant-criterion-for-infinitesimal-homeostasis.md)).

**Combinatorial notions.**
- A *simple path* visits each node at most once; an $\iota o$-*simple path* joins $\iota$ to $o$. A node is *simple* if it lies on some $\iota o$-simple path and *appendage* otherwise; it is *super-simple* if it lies on every $\iota o$-simple path ($\iota$ and $o$ are super-simple). Super-simple nodes are totally ordered by the downstream order: $\iota=\rho_1>\rho_2>\cdots>\rho_{q+1}=o$.
- The *appendage subnetwork* $\mathcal{A}_\mathcal{G}$ is spanned by the appendage nodes; its *appendage path components* are its strongly connected components. For an $\iota o$-simple path $S$, the complementary subnetwork $\mathcal{C}_S$ is spanned by the nodes off $S$. A subnetwork $\mathcal{K}\subseteq\mathcal{A}_\mathcal{G}$ satisfies the *no cycle condition* if for every $\iota o$-simple path $S$, nodes of $\mathcal{K}$ form no cycle with nodes of $\mathcal{C}_S\setminus\mathcal{K}$. This splits $\mathcal{A}_\mathcal{G}=(\mathcal{A}_1\sqcup\cdots\sqcup\mathcal{A}_s)\sqcup(\mathcal{B}_1\sqcup\cdots\sqcup\mathcal{B}_t)$ into no-cycle components $\mathcal{A}_i$ and cycle components $\mathcal{B}_j$.
- For adjacent super-simple nodes $\rho_i,\rho_{i+1}$, the *super-simple structural subnetwork* $\mathcal{L}'(\rho_i,\rho_{i+1})$ consists of the simple nodes lying between $\rho_i$ and $\rho_{i+1}$ on some $\iota o$-simple path, together with every cycle component $\mathcal{B}_j$ that forms cycles with them; it is an input-output network with input $\rho_i$ and output $\rho_{i+1}$.

**Classification.** The homeostasis blocks of $\mathcal{G}$ are exactly $m=s+q$ in number:
1. *Appendage homeostasis*: the $s$ no-cycle appendage path components $\mathcal{A}_1,\dots,\mathcal{A}_s$, with defining conditions $\det J_{\mathcal{A}_i}=0$, where $J_{\mathcal{A}_i}$ is the Jacobian of the subnetwork $\mathcal{A}_i$.
2. *Structural homeostasis*: the $q$ subnetworks $\mathcal{L}'(\rho_i,\rho_{i+1})$, $i=1,\dots,q$, with defining conditions $\det H\big(\mathcal{L}'(\rho_i,\rho_{i+1})\big)=0$, the homeostasis matrix of that input-output subnetwork.

Thus all mechanisms by which $x_o'(\mathcal{I}_0)=0$ can occur generically are read off from the graph, without simulating any particular model.

**Input = output networks.** If the input and output nodes coincide, $H$ is the Jacobian $f_{\rho,x_\rho}$ of the regulatory nodes. A regulatory node lies in the core subnetwork if and only if it lies on a cycle through the input = output node; in a core input = output network every node is appendage (Lemma 2.14), so structural homeostasis does not occur (Corollary 2.15), and the irreducible factors of $\det H$ are exactly $\det J(\mathcal{A}_k)$ over the appendage path components $\mathcal{A}_k$ of the regulatory subnetwork (Theorem 2.16).

## Depends on

- [Determinant criterion for infinitesimal homeostasis](determinant-criterion-for-infinitesimal-homeostasis.md)

## Expansion

An irreducible block of $H$ either involves only appendage nodes, in which case its rows and columns are those of an appendage path component and the block equals that component's Jacobian (the no cycle condition is what prevents the component from mixing with entries along every simple path), or it contains the entries along a stretch of the $\iota o$-simple paths between two consecutive super-simple nodes, since every simple path passes through each super-simple node and $\det H$ factors at each one. The combinatorial classification is implemented as a graph algorithm: compute the core subnetwork, enumerate $\iota o$-simple paths, classify nodes, take strongly connected components of $\mathcal{A}_\mathcal{G}$ and test the no cycle condition, then cut the structural subnetwork at the super-simple nodes. It has been applied to cholesterol, chemotaxis, dopamine, one-carbon metabolism and zinc homeostasis networks, with the blocks verified by direct factorization of $\det H$.

## Sources

- Xinni Lin, Fernando Antoneli, Yangyang Wang, "Automated Classification of Homeostasis Structure in Input-Output Networks", *Bulletin of Mathematical Biology* 88(7) (2026), 113, Definitions 2.5-2.11, Lemma 2.14, Corollary 2.15, Theorem 2.16 and the classification algorithm of Section 2.1, <https://doi.org/10.1007/s11538-026-01679-3> (preprint arXiv:2603.08882). The single-input classification is due to Wang, Huang, Antoneli and Golubitsky (2021).
