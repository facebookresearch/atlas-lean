# Modified μ-representation encodes semi-binary stack-free orchard networks

**Setting.** A *phylogenetic network* on a finite leaf set $X$ is a rooted directed acyclic graph without parallel arcs or elementary (in-degree $1$, out-degree $1$) nodes, whose leaves are bijectively labeled by $X$, whose reticulations (in-degree $\ge2$) have out-degree $1$, and whose root has out-degree $\ge2$ unless $|X|=1$. It is *semi-binary* if every tree-node other than the root and the leaves has degree $3$ (reticulations may have any in-degree $\ge2$), *stack-free* if no reticulation is the child of a reticulation, and *orchard* if it can be reduced to a single leaf by repeatedly reducing cherries $(a,b)$ (two leaves with a common parent; delete $b$) and reticulated cherries $(a,b)$ (the parent $p_b$ of $b$ is a reticulation whose parent is the parent $p_a$ of $a$; delete the arc $p_ap_b$), suppressing elementary nodes after each step.

For a node $v$, the **μ-vector** $\mu(v)\in\mathbb{Z}_{\ge0}^X$ has $a$-coordinate equal to the number of directed paths from $v$ to leaf $a$; the **μ-representation** $\mu(N)$ is the multiset $\{\mu(v):v\in V(N)\}$. The **modified μ-vector** prepends the in-degree, $\mu^\ast(v)=\delta^-(v)\oplus\mu(v)\in\mathbb{Z}^{1+|X|}$, and $\mu^\ast(N)$ is the multiset of modified μ-vectors.

**Theorem (encoding).** Let $N_1$ be a semi-binary stack-free orchard network and $N_2$ a semi-binary stack-free network on the same leaf set. Then

$$\mu^\ast(N_1)=\mu^\ast(N_2)\iff N_1\cong N_2 .$$

Consequently the **μ\*-distance**

$$d_{\mu^\ast}(N_1,N_2)=\bigl|\mu^\ast(N_1)\,\triangle\,\mu^\ast(N_2)\bigr|,$$

the cardinality of the multiset symmetric difference (each element counted with the absolute difference of its multiplicities), is a metric on the class of semi-binary stack-free orchard networks.

**Theorem (non-binary failure).** Non-binary stack-free orchard networks are *not* encoded by their modified μ-representation: there exist two non-isomorphic stack-free orchard networks with equal $\mu^\ast$-representations (and equal out-degrees at corresponding nodes), differing only at a tree-node of out-degree $3$.

## Expansion

Leaves have unit μ-vectors and every internal node's μ-vector is the sum of its children's. In a stack-free network the μ-representation reveals whether $(a,b)$ is a cherry (the vector $\mu(a)+\mu(b)$ is present as the parent) or a reticulated cherry, and the in-degree coordinate of $\mu^\ast$ tells whether $p_b$ has in-degree $2$ (it disappears on reduction) or more (its in-degree drops by one). Each reduction therefore has a unique counterpart acting on the multiset $\mu^\ast(N)$, which commutes with the network reduction. Because $N_1$ is orchard, the same reduction sequence applies step by step to $N_2$ and ends at the same single leaf; since a network is recovered uniquely from its reduced network by reversing one reduction, induction backwards along the sequence gives $N_1\cong N_2$. Without the in-degree coordinate the plain μ-representation fails even for semi-binary stack-free networks, and in the non-binary case a node of out-degree $3$ can have its μ-vector written as two different sums of children's vectors, so reticulated cherries are no longer determined.

## Sources

- Christopher Reichling, Leo van Iersel and Yukihiro Murakami, "Metrics for classes of semi-binary phylogenetic networks using μ-representations", Advances in Applied Mathematics 172 (2026), 102953, <https://doi.org/10.1016/j.aam.2025.102953>; numbering as in arXiv:2412.05107: Section 2 and Section 3: Definition 1, Lemmas 1–3, Theorem 1, Section 3.3 ($\mu^\ast$-distance), Theorem 2.
- G. Cardona, F. Rosselló, G. Valiente, "Comparison of tree-child phylogenetic networks", IEEE/ACM Transactions on Computational Biology and Bioinformatics 6 (2009) 552–569, <https://doi.org/10.1109/TCBB.2007.70270> (μ-representation encodes tree-child networks).
