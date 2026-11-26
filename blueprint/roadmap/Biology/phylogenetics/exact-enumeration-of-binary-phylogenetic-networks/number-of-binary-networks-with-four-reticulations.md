# Number of binary phylogenetic networks with four reticulations

A **rooted binary phylogenetic network** on $[n]$ is a rooted acyclic digraph without parallel arcs whose root has out-degree 2, whose $n$ leaves (out-degree 0) are labelled bijectively by $[n]$, and whose other vertices are tree vertices (in-degree 1, out-degree 2) or reticulations (in-degree 2, out-degree 1). With $k$ reticulations such a network has $2n+3k-1$ arcs. Let $\mathcal P_{n,k}$ be the set of these networks with $k$ reticulations (no further class restriction such as tree-child or normal).

**Building blocks.** The number of rooted binary forests on $[n]$ with $k$ trees is

$$|\mathcal F_{n,k}|=\frac{(2n-k-1)!}{2^{n-k}(n-k)!(k-1)!},$$

so there are $t_n=(2n-3)!!$ binary trees. Deleting all reticulation arcs splits a network into **tree components**; contracting each component gives its **component graph**, a small DAG recording how reticulations connect components.

**Theorem.** For $n\ge 2$,

$$|\mathcal P_{n,4}|=\frac{(2n-4)!}{189\,(n-2)!\,2^{n-1}}\,Q_9(n)-\frac{1}{3}(n+1)!\,2^{n-4}\big(32n^5+558n^4+3901n^3+13523n^2+23008n+15264\big),$$

$$Q_9(n)=504n^9+10836n^8+91414n^7+362607n^6+568813n^5-326256n^4-1950557n^3-1378566n^2+440523n+367416,$$

and $|\mathcal P_{1,4}|=109$. The first values are $3881,\ 113424,\ 3212190,\ 92486235,\ 2759501745$ for $n=2,\dots,6$.

## Expansion

The 79 component graphs possible with four reticulations are sorted into ten groups. For each group the networks are counted by choosing a forest of tree components on the labelled leaves, then attaching the reticulation arcs, using known counts of one-component networks (networks whose reticulations each have a leaf child), of forests $|\mathcal F_{n,k}|$, and of networks with fewer reticulations; each count is a sum over binomial convolutions simplified with central-binomial identities such as $\sum_{k=0}^n\binom{2k}{k}\binom{2n-2k}{n-k}=4^n$. Summing the ten group totals gives the formula for $n\ge4$; for $n=2,3$ the groups that become empty contribute zero and the same expression still holds, while $n=1$ is computed directly as $45+31+3+22+8$. The two terms reflect two growth regimes: a $(2n)!/n!$-type term from configurations dominated by large tree components, and an $n!\,2^n$-type term from one-component-like configurations. The formula extends the earlier closed forms for $k\le 3$ obtained by the same method.

## Sources

- H. Yu, L. Zhang, "Exact counts of binary phylogenetic networks with four reticulations", arXiv:2609.21772 (2026), Propositions 2.1-2.3, Lemma 2.4, Lemmas 3.1-3.10, Theorem 3.11 and Table of counts for $1\le n\le 12$, <https://doi.org/10.48550/arXiv.2609.21772>.
