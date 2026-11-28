# Asymptotic count of tree-child and normal networks with a fixed number of reticulations

A *phylogenetic network* here is a rooted binary phylogenetic network: a connected rooted directed acyclic graph whose root has in-degree $0$ and out-degree $2$ (except for the network consisting of a single vertex), whose other non-leaf vertices are tree vertices (in-degree $1$, out-degree $2$) or reticulation vertices (in-degree $2$, out-degree $1$), with leaves of in-degree $1$. It is *tree-child* if every non-leaf vertex has a child that is not a reticulation, and *normal* if it is tree-child and has no arc $(u,v)$ for which another directed path from $u$ to $v$ exists. Let $N_{k,n}$ and $T_{k,n}$ count vertex-labelled normal and tree-child networks with $n$ vertices and $k$ reticulations, and $\tilde N_{k,\ell}$, $\tilde T_{k,\ell}$ the leaf-labelled ones with $\ell$ leaves.

**Theorem.** Fix $k \ge 1$. There is $c_k > 0$ such that

$$
N_{k,n} \sim c_k \big(1 - (-1)^n\big) \Big(\frac{\sqrt2}{e}\Big)^n n^{n+2k-1} \qquad (n \to \infty),
$$

with $c_1 = \sqrt2/4$, $c_2 = \sqrt2/32$, $c_3 = \sqrt2/384$; the same first-order asymptotics hold for $T_{k,n}$. In the leaf-labelled case

$$
\tilde N_{k,\ell} \sim \tilde T_{k,\ell} \sim 2^{3k-1} c_k \Big(\frac{2}{e}\Big)^{\ell} \ell^{\ell+2k-1} \qquad (\ell \to \infty).
$$

In particular, for each fixed $k$, asymptotically almost all tree-child networks with $k$ reticulations are normal.

## Expansion

Removing one incoming arc of each reticulation decomposes a network into a forest of trees with $k$ marked attachment points; the exponential generating function of vertex-labelled networks with $k$ reticulations is therefore algebraic in the tree function, of the form $z\,(\tilde a_k(z^2) - \tilde b_k(z^2)\sqrt{1-2z^2})/(1-2z^2)^{2k-1/2}$, and singularity analysis at $z = 1/\sqrt2$ gives the $n^{n+2k-1}$ growth. Tree-child and normal counts differ only in second-order terms (e.g. $\sqrt2/2 - \tfrac{\sqrt\pi}{2} n^{-1/2}$ against $\sqrt2/2 - \tfrac{3\sqrt\pi}{2} n^{-1/2}$ for $k=1$, after factoring $(\sqrt2/e)^n n^{n+1}$). For $k = 0$ the formula reduces to Schröder's count of phylogenetic trees. The asymptotic equivalence is not uniform in $k$.

## Sources

- Michael Fuchs, Bernhard Gittenberger and Marefatollah Mansouri, *Counting Phylogenetic Networks with Few Reticulation Vertices: Tree-Child and Normal Networks*, arXiv:1803.11325, Section 1 (definition (i)–(iii) of phylogenetic networks), Theorems 1 and 2 (Section 1), Theorem 3 (Section 5) and Corollaries 1–9. <https://doi.org/10.48550/arXiv.1803.11325> Published version: Australasian Journal of Combinatorics 73 (2019) 385–423.
