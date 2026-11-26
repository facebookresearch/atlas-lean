# Minimum remaining gap cost heuristic for partial order alignment

Let $G = (V, E)$ be a partial order alignment (POA) graph: a DAG of character-labelled nodes with a start node $\nu$ and end node $\tau$. Aligning a query $Q = q_1 \cdots q_m$ to $G$ means choosing a path $\nu v_1 \cdots v_n \tau$, spelling $R$, and an alignment of $Q$ to $R$ of minimum cost. With linear gap penalties the cost is $C = N_m\Delta_m + N_x\Delta_x + N_g\Delta_g$ for $N_m$ matches, $N_x$ mismatches and total gap length $N_g$, where $\Delta_m = 0$ and $\Delta_x, \Delta_g \ge 0$. Alignment states are pairs $\langle v, i\rangle$ (node $v$, query prefix length $i$), and an optimal alignment is a least-cost path from $\langle \nu, 0\rangle$ to $\langle \tau, m\rangle$ in the alignment graph whose edges are matches or mismatches ($\langle u,i\rangle \to \langle v,i+1\rangle$), insertions ($\langle u,i\rangle \to \langle u,i+1\rangle$) and deletions ($\langle u,i\rangle \to \langle v,i\rangle$) for $(u,v) \in E$.

For each node let $d^{\min}_{v,\tau}$ and $d^{\max}_{v,\tau}$ be the shortest and longest path lengths (in edges) from $v$ to $\tau$, computable in $O(|V| + |E|)$ in reverse topological order, and let $l_r = m - i$ be the unaligned query length.

**Definition (minimum number of indels).**

$$N_g^{\min}\langle v,i\rangle = \begin{cases} l_r - (d^{\max}_{v,\tau} - 1), & d^{\max}_{v,\tau} - 1 < l_r,\\ (d^{\min}_{v,\tau} - 1) - l_r, & d^{\min}_{v,\tau} - 1 > l_r,\\ 0, & \text{otherwise.}\end{cases}$$

**Lemma (admissibility).** The heuristic $h\langle v,i\rangle = N_g^{\min}\langle v,i\rangle\,\Delta_g$ is a lower bound on the cost of completing the alignment from $\langle v, i\rangle$, so A* with $h$ returns an optimal alignment.

**Greedy matches.** Since matches cost $0$ and all other edges cost $\ge 0$, an unvisited match successor $\langle v, i+1\rangle$ of $\langle u, i\rangle$ can be taken immediately, ignoring the insertion and deletion edges at $\langle u, i\rangle$, without losing optimality.

**Superbubble pruning.** If $(s,t)$ is a superbubble (single entrance $s$, single exit $t$, every path from $s$ ends at $t$) and the exit state $\langle t, p\rangle$ has been reached at cost $C$, then a state $\langle v, i\rangle$ with $v$ in the bubble can reach only $\langle t, j\rangle$ for $j \in [\,i + d^{\min}_{v,t},\ i + d^{\max}_{v,t}\,]$ at its own cost or more, and can be pruned when none of these can improve on already-reached exit states.

## Expansion

Any completion from $\langle v,i\rangle$ follows some path from $v$ to $\tau$ with between $d^{\min}_{v,\tau} - 1$ and $d^{\max}_{v,\tau} - 1$ character nodes and must consume $l_r$ query characters. If the query remainder is longer than the longest path, at least $l_r - (d^{\max} - 1)$ insertions are forced; if shorter than the shortest path, at least $(d^{\min} - 1) - l_r$ deletions. Hence $N_g \ge N_g^{\min}$ and $C_r = N_x\Delta_x + N_g\Delta_g \ge N_g^{\min}\Delta_g$. This generalizes the classical gap-cost (diagonal-distance) heuristic for pairwise alignment, where both path lengths equal the remaining reference length. Interleaving depth-first extension of exact matches with the A* queue, as in wavefront alignment, and pruning inside superbubbles means only a small fraction of the $O(|V|m)$ dynamic-programming states is computed. The resulting optimal gap-affine POA algorithm, POASTA, has preprocessing linear in the graph size.

## Sources

- L. R. van Dijk, A. L. Manson, A. M. Earl, K. V. Garimella, T. Abeel, "Fast and exact gap-affine partial order alignment with POASTA", Bioinformatics (2024) btae757, Sections 2.1–2.4, Definitions 1–2 and Lemma 1, <https://doi.org/10.1093/bioinformatics/btae757>, PMCID PMC11755094.
