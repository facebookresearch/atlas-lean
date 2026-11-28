# Block-graph reduction of AND-quantification to OR-quantification

**Setting.** Let $G$ be a DAG with source $S$, sink $T$ and a flow $F$ of total value $U$. Let $E_1,\dots,E_m\subseteq E$ be edge sets with the *well-ordering property*: if a path visits $e_i\in E_i$ and later $e_j\in E_j$, then $i<j$. An $S$–$T$ path is *good* if it meets every $E_k$. The problem $\mathrm{AND\text{-}Quant}(G,\{E_k\})$ asks for the minimum and maximum, over all decompositions of $F$, of the total weight on good paths. For a full transcript, each $E_k$ is the single edge of its $k$-th junction. For a local splicing pattern, each $E_k$ is the set of edges encoding one junction.

**Block graph.** After discarding edges of the $E_i$ that lie on no good path, let $U_i$ and $V_i$ be the tails and heads of the edges in $E_i$, with $V_0=\{S\}$ and $U_{m+1}=\{T\}$. Write $x\le y$ if there is a directed path from $x$ to $y$. Let $B_i$ be the set of edges $(u,v)$ with $V_{i-1}\to u$ and $v\to U_i$, where $V_{i-1}\to u$ means $v'\le u$ for some $v'\in V_{i-1}$ and $v\to U_i$ means $v\le u'$ for some $u'\in U_i$. The block graph is $G_B=\bigcup_i(B_i\cup E_i)$.

**Lemma.** An $S$–$T$ path of $G$ is good if and only if it is contained in $G_B$.

**Theorem.** If $[l,r]=\mathrm{OR\text{-}Quant}(G,\,E\setminus G_B)$, then

$$\mathrm{AND\text{-}Quant}(G,\{E_k\})=[\,U-r,\ U-l\,].$$

The filtering and the construction of all $B_i$ take $O(|V|+|E|)$ time.

## Depends on

- [Max-flow bounds on good flow over all flow decompositions](max-flow-bounds-on-good-flow-over-all-flow-decompositions.md)

## Expansion

By the lemma, a path is bad for AND-Quant exactly when it uses an edge outside $G_B$. The bad flow is therefore an OR-Quant instance on the complement, and good flow is $U$ minus it. The "only if" direction of the lemma is immediate. For "if", the well-ordering property gives that for each $i$ every vertex of $G_B$ either reaches $U_i$ or is reached from $V_i$, but not both. Hence $E_i$ is an $S$–$T$ cut of $G_B$, and every path in $G_B$ meets every $E_i$. For the linear-time construction, a forward pass in topological order computes $s(v)$, the largest $i$ such that $v$ is reached through edges of $E_1,\dots,E_i$ in order, and a backward pass computes the analogous $t(v)$. An edge $(u,v)\in E_i$ is kept iff $s(u)=i-1$ and $t(v)=i+1$, and any other edge goes to $B_{t(v)}$ iff $s(u)+1=t(v)$.

## Sources

- H. Zheng, C. Ma, C. Kingsford, "Deriving ranges of optimal estimated transcript expression due to nonidentifiability", *Journal of Computational Biology* 29(2):121–139 (2022), Section 2.4 (Definition 1, Lemma 1, Theorem 2), Section 2.4.2 (Definitions 7–10, Lemmas 3–7), Section 2.4.3 (Lemma 8), <https://doi.org/10.1089/cmb.2021.0444>, PMCID PMC8892959.
