# Pons-Batle identity for tree-child networks

A *rooted binary phylogenetic network* on a taxon set of size $n$ is a directed acyclic graph with a root of indegree $0$ and outdegree $1$, *tree nodes* of indegree $1$ and outdegree $2$, *reticulation nodes* of indegree $2$ and outdegree $1$, and $n$ leaves of indegree $1$ bijectively labeled by the taxa. It is *tree-child* if every non-leaf node has a child that is a tree node or a leaf. A tree node is *free* if neither of its children is a reticulation; an edge entering a tree node or a leaf is a *tree edge*. Let $a_{n,k}$ be the number of tree-child networks with $k$ reticulations on a fixed set of $n$ taxa, with $a_{n,k}=0$ unless $n\ge1$ and $0\le k<n$.

**Theorem (Pons-Batle identity).** For $n\ge2$ and $0\le k<n$,

$$a_{n,k}=(n-k+1)\,a_{n,k-1}+\frac{n(2n+k-3)}{n-k}\,a_{n-1,k}.$$

**Leaf-type reformulation.** In a tree-child network a leaf is a *child leaf* if its parent is a reticulation, a *side leaf* if its sibling is a reticulation, and a *free leaf* otherwise. Let $H(n,k)$ count pairs (network, child or side leaf) and $\Gamma(n,k)$ pairs (network, free leaf) over all networks counted by $a_{n,k}$, so $H(n,k)+\Gamma(n,k)=n\,a_{n,k}$. Then

$$\Gamma(n,k)=n(2n+k-3)\,a_{n-1,k},$$

and the Pons-Batle identity is equivalent to

$$H(n,k)=k\,a_{n,k}+(n-k)(n-k+1)\,a_{n,k-1}\qquad(n\ge1,\ 0\le k<n),$$

which is proved by showing that both sides satisfy the same root-decomposition recurrence.

**Root-decomposition recurrence.** Splitting a network at the child of its root into a source and a target subnetwork joined by $c$ cross reticulation edges gives, for $n\ge2$ and $0\le k<n$,

$$2\,a_{n,k}=\sum_{m+p=n,\ i+j+c=k}K_0\,a_{m,i}\,a_{p,j},$$

with an explicit combinatorial kernel $K_0$ counting the ways to insert the cross edges between a source network with $m$ taxa and $i$ reticulations and a target network with $p$ taxa and $j$ reticulations.

## Depends on

- [Node and edge counts of tree-child networks](node-and-edge-counts-of-tree-child-networks.md)

## Expansion

Deleting a free leaf and suppressing its parent leaves a tree-child network on $n-1$ taxa with the same $k$; conversely a new leaf can be attached by subdividing any of the $2(n-1)+k-1$ tree edges of a network on $n-1$ taxa, with $n$ choices for which taxon it carries, and it is then free, which gives $\Gamma(n,k)$. Substituting $H=n\,a_{n,k}-\Gamma$ into the reformulated identity recovers the Pons-Batle identity. To prove the reformulation, the authors refine the kernel $K_0$ into four kernels tracking where marked leaves fall in the root split, show that $H$ and the candidate right-hand side satisfy the same recurrence with the same initial values, and conclude they coincide. The identity was first conjectured by Pons and Batle and earlier proved through Young tableaux with walls.

## Sources

- H. Yu and L. Zhang, "A Short Combinatorial Proof of the Pons-Batle Identity for Counting Tree-Child Networks", arXiv preprint (2026), <https://doi.org/10.48550/arXiv.2609.04979>. Section 1 (the identity), Proposition 2.1, Lemma 3.2, Definition 3.3, Lemma 3.4, Proposition 3.5, Lemma 4.1, Theorem 4.2, Definition 5.1, Lemma 5.2, Proposition 5.3, Lemma 6.2, Proposition 6.3 and Theorem 6.4.
