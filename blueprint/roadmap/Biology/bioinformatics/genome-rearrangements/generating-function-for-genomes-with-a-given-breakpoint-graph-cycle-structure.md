# Generating function for genomes with a given breakpoint-graph cycle structure

**Breakpoint graphs.** Represent a circular multichromosomal genome on genes $\{1, \dots, n\}$ by its genome graph: vertices $i^t, i^h$ (tail and head of gene $i$), directed gene edges $(i^t, i^h)$, and undirected adjacency edges joining the extremities of neighbouring genes. For two genomes $P, Q$ on the same genes, the **breakpoint graph** $G(P, Q)$ has the adjacency edges of $P$ (black) and of $Q$ (gray). Every vertex has degree $2$, so $G(P,Q)$ is a disjoint union of alternating cycles; an **$\ell$-cycle** has $\ell$ black and $\ell$ gray edges. The **cycle structure** of $G(P,Q)$ is $\mathbf{c} = (c_1, c_2, \dots)$, with $c_\ell$ the number of $\ell$-cycles, so that $L(\mathbf{c}) = \sum_\ell \ell c_\ell = n$. A $k$-break replaces $k$ gray edges by $k$ other gray edges on the same $2k$ vertices. The $k$-break distance from $Q$ to $P$ depends only on $\mathbf{c}$; for example $d_2(P, Q) = n - \sum_\ell c_\ell$.

**Counting problem.** Fix a unichromosomal circular genome $P$ with $n$ genes. Let $M_n(h; \mathbf{c})$ be the number of $h$-chromosomal genomes $Q$ (genes of arbitrary orientation) with $G(P,Q)$ of cycle structure $\mathbf{c}$, and $M_n^+(h; \mathbf{c})$ the number with all genes co-oriented. Define

$$
F(x; u; s_1, s_2, \dots) = \sum_{\mathbf{c}} x^{L(\mathbf{c}) - 1}\sum_{h \ge 1} M_{L(\mathbf{c})}(h; \mathbf{c})\, u^{h-1}\prod_{i \ge 1} s_i^{c_i},
$$

and $G(x; u; s_1, s_2, \dots)$ in the same way with $M^+$ in place of $M$.

**Theorem (arbitrary orientations).** $F$ is the unique solution of

$$
\frac{\partial F}{\partial x} = \sum_{i \ge 2}\sum_{j=1}^{i-1}(i-1)\,s_j s_{i-j}\,\frac{\partial F}{\partial s_{i-1}} + \sum_{i \ge 2}(i-1)^2 s_i\,\frac{\partial F}{\partial s_{i-1}} + 2\sum_{i \ge 2}\sum_{j=1}^{i-1} j(i-j)\,s_{i+1}\,\frac{\partial^2 F}{\partial s_j\,\partial s_{i-j}} + u\sum_{i \ge 1} i\,s_{i+1}\,\frac{\partial F}{\partial s_i}
$$

with $F(0; u; s_1, s_2, \dots) = s_1$.

**Theorem (co-oriented genes).** $G$ is the unique solution of

$$
\frac{\partial G}{\partial x} = \sum_{i \ge 2}\sum_{j=1}^{i-1}(i-1)\,s_j s_{i-j}\,\frac{\partial G}{\partial s_{i-1}} + \sum_{i \ge 2}\sum_{j=1}^{i-1} j(i-j)\,s_{i+1}\,\frac{\partial^2 G}{\partial s_j\,\partial s_{i-j}} + u\sum_{i \ge 1} i\,s_{i+1}\,\frac{\partial G}{\partial s_i}
$$

with $G(0; u; s_1, s_2, \dots) = s_1$. For example, the unichromosomal coefficients ($u = 0$) begin $F_3 = s_1^3 + 3 s_1 s_2 + 4 s_3$ and $G_5 = s_1^5 + 10 s_1^2 s_3 + 5 s_1 s_2^2 + 8 s_5$.

**Corollary (generalized Hultman numbers).** Setting $u = 0$ and all $s_i = s$ in $G$ gives $G_n(0; s, s, \dots) = \sum_{m} H(n-1, m)\, s^m$, so the Hultman number, the number of unsigned permutations of $n-1$ elements whose breakpoint graph has $m$ cycles, is

$$
H(n-1, m) = \sum_{\mathbf{c}:\, L(\mathbf{c}) = n,\ \sum_i c_i = m} M_n^+(1; \mathbf{c}) .
$$

The same sum with $M_n(1; \mathbf{c})$ gives the signed Hultman numbers $H^{\pm}(n-1, m)$. Summing over $\mathbf{c}$ by $k$-break distance gives the distribution of $k$-break distances from a fixed genome for every $k \ge 2$.

## Expansion

The recurrence behind the PDE removes one gene, say gene $n$, from $Q$ and tracks how the breakpoint graph changes. Contracting the gene's extremities either merges two cycles of lengths $j$ and $i-j$ into an $(i-1)$-cycle (first term), shortens a cycle that contains both extremities (second term, which exists only when the gene can be flipped, hence absent for co-oriented genomes), splits an $(i+1)$-cycle into two (third term, with factor $2$ for the two orientations), or deletes a one-gene chromosome (the $u$ term). Reversing this deletion step gives $(n-1)M_n(h;\mathbf{c})$ as a weighted sum of counts with $n-1$ genes, which determines all coefficients by induction from $F = s_1$ at $n = 1$. Since $k$-break distances depend only on cycle lengths, the counts give the exact distribution of rearrangement distances, including $k > 3$, which models chromothripsis in cancer genomes.

## Sources

- Nikita Alexeev, Anna Pologova and Max A. Alekseyev, "Generalized Hultman Numbers and Cycle Structures of Breakpoint Graphs", arXiv (2015), Section 2 (genome and breakpoint graphs, $k$-breaks), Section 3 (Theorem 3.1 and Lemma 3.2), Section 4 (Theorem 4.1 and Hultman number formulas), <https://doi.org/10.48550/arXiv.1503.05285>.
- A. Hultman, "Toric permutations", Master's thesis, KTH Stockholm (1999).
