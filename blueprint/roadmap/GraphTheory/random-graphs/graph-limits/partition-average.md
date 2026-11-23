# Partition average of a weighted graph

For a partition $\mathcal P = \{V_1, \dots, V_k\}$ of the vertex set of a weighted graph $G$ (unit node weights), $G_{\mathcal P}$ is the weighted graph on the same vertices whose weight on $xy$, for $x \in V_i$ and $y \in V_j$, is the average

$$\frac{e_G(V_i, V_j)}{|V_i| \, |V_j|} = \frac{1}{|V_i| |V_j|} \sum_{a \in V_i} \sum_{b \in V_j} \beta_{ab}(G).$$

It is the step-function approximation of $G$ with steps $\mathcal P$ that the weak regularity lemma uses.

## Sources

- C. Borgs, J. T. Chayes, L. Lovász, V. T. Sós and K. Vesztergombi, "Convergent sequences of dense graphs I: Subgraph frequencies, metric properties and testing", *Adv. Math.* 219 (2008), 1801–1851, arXiv:math/0702004, §2.4 (the graphs $G/\mathcal P$ and $G_{\mathcal P}$).
