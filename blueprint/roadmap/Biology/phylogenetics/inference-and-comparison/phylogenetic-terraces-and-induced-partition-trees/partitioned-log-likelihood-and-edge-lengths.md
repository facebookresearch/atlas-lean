# Partitioned log-likelihood and the edge lengths of induced partition trees

Let $T$ be a species tree on $X$ with edge set $E$, let $Y_1, \dots, Y_k$ be partition species sets with alignments $S_1, \dots, S_k$ and substitution models $M_1, \dots, M_k$, and let $f_i : E \to E_i \cup \{\epsilon\}$ be the [edge maps](induced-partition-tree-edge-map.md).

**Definition and theorem (additivity).** Under a partition model $M = (M_1, \dots, M_k)$ the log-likelihood of the species tree is the sum of the partition log-likelihoods,

$$\ell(T, M \mid S) \;=\; \sum_{i=1}^{k} \ell\bigl(T|_{Y_i}, M_i \mid S_i\bigr),$$

each term depending on $T$ only through the topology and edge lengths of $T|_{Y_i}$.

**Edge-length models.** Write $\lambda_i(\cdot)$ for the edge lengths of $T|_{Y_i}$ and $\lambda(\cdot)$ for those of $T$.
- *Edge-unlinked:* each $\lambda_i$ is free and optimized separately per partition tree; $T$ carries no edge lengths of its own.
- *Edge-linked proportional:* there is one set $\lambda$ on $T$ and positive partition rates $r_1, \dots, r_k$ with $\sum_i w_i r_i / \sum_i w_i = 1$, where $w_i$ is the length of $S_i$, and

$$\lambda_i(e') \;=\; r_i \sum_{e \in E \,:\, f_i(e) = e'} \lambda(e), \qquad e' \in E_i .$$

- *Edge-linked equal:* the special case $r_1 = \cdots = r_k = 1$.

Two consequences. First, under the edge-unlinked model an interchange that leaves $T|_{Y_i}$ unchanged leaves the optimal value of the $i$-th term unchanged, so terms on a partial terrace are reused verbatim. Second, under either edge-linked model the optimization of one edge $e \in E$ only needs the terms with $f_i(e) \neq \epsilon$, because the remaining terms do not depend on $\lambda(e)$.

## Depends on

- [Induced partition tree and the edge map of a supermatrix](induced-partition-tree-edge-map.md)

## Proof sketch

Additivity holds because distinct partitions are modelled as independent, and a species absent from partition $i$ contributes only gap characters there, so the $i$-th alignment's likelihood is computed on the pruned tree $T|_{Y_i}$. The edge-length formula is the statement that pruning and suppressing degree-two vertices adds the lengths of all edges merged into one edge of the induced tree; the fibre $f_i^{-1}(e')$ is exactly the set of merged edges, which is why the data structure stores the map rather than only the trees. Under the edge-unlinked model each $\lambda_i$ is optimized freely, so equality of topologies gives equality of optimized scores; under edge-linked models equal topologies may still carry different edge lengths after a rearrangement, and only the weaker saving of re-optimizing fewer edges is available, with the extreme case of three or more of the four flanking edges mapping to $\epsilon$, where nothing changes at all.

## Sources

- O. Chernomor, A. von Haeseler and B. Q. Minh, "Terrace aware data structure for phylogenomic inference from supermatrices", Systematic Biology 65 (2016), 997–1008, Eqs. (1) and (5), Partition Models section and Appendix 2, <https://doi.org/10.1093/sysbio/syw037>, PMCID: PMC5066062.
