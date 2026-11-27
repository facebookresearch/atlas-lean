# Constrained k-Dollo phylogeny with copy-number clones

Let $A \in \{0,1\}^{n\times m}$ be a cell-by-mutation matrix over somatic SNVs and germline SNPs, and let $\sigma : \{1,\dots,n\} \to \{1,\dots,p\}$ be a clustering of cells into copy-number clones. A **constrained $k$-Dollo phylogeny** for $(A, \sigma)$ is a rooted tree $T$ with $n$ leaves labelled by the rows of $A$ and their clones, each node $v$ labelled by $a_v \in \{0,1\}^m$ and a clone $\sigma(v)$, such that

1. the root has $a_{r,j} = 0$ for SNVs and $a_{r,j} = 1$ for SNPs;
2. each mutation is gained ($0 \to 1$) on at most one edge;
3. each mutation is lost ($1 \to 0$) on at most $k$ edges;
4. every loss edge $(v,w)$ joins different clones, $\sigma(v) \ne \sigma(w)$ (losses are caused by copy-number aberrations);
5. the nodes of each clone form a connected subtree.

For $p = 1$ this is the infinite-sites model; for $p = n$ it is the unconstrained $k$-Dollo model.

A $k$-Dollo completion $B$ of $A$ is **consistent** with $\sigma$ if, for every mutation $j$: at most one clone $\ell$ contains cells $i, i'$ with $b_{i,j} = 0$ and $b_{i',j} = 1$ (the gain happens inside at most one clone), and if some cell of clone $\ell$ has loss state $b_{i,j} = s \in \{2, \dots, k+1\}$ then every cell of $\ell$ has $b_{i',j} = s$; and $b_{i,j} \ge 1$ for every cell $i$ and every SNP column $j$.

**Theorem (characterization).** $A$ is a constrained $k$-Dollo phylogeny matrix for $\sigma$ if and only if it has a $k$-Dollo completion consistent with $\sigma$; given such a completion, a constrained $k$-Dollo phylogeny is constructed in $O(nmk)$ time.

**Theorem (hardness).** Finding $A$ and $T$ that maximize a read-count likelihood $\Pr(Q \mid R, A)$ subject to $T$ being a constrained $k$-Dollo phylogeny for $(A,\sigma)$ is NP-hard, even for $k = 0$.

## Depends on

- [k-Dollo completions characterize k-Dollo phylogeny matrices](k-dollo-completions-characterize-k-dollo-phylogeny-matrices.md)

## Expansion

Consistency translates conditions 4 and 5 into the completion: a loss inside a clone would put a loss edge between same-clone nodes, and a clone split across a loss state could not be connected. The characterization lets the method encode the search as a mixed-integer linear program over completion entries with the forbidden-submatrix and consistency constraints, maximizing a beta-binomial likelihood of variant and total read counts.

## Sources

- P. Sashittal, H. Zhang, C. A. Iacobuzio-Donahue and B. J. Raphael, "ConDoR: tumor phylogeny inference with a copy-number constrained mutation loss model", Genome Biology 24 (2023), Results ("Constrained k-Dollo model", Definition 1, Problem 1) and Methods (Definition 4, Theorems 2–3), <https://doi.org/10.1186/s13059-023-03106-5>, PMCID: PMC10688497.
