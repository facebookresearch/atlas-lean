# Tanglegram isomorphism classes as double cosets

Let $T$ and $S$ be (rooted or unrooted) trees with $n$ leaves each, with leaf sets $L(T)$ and $L(S)$. An **ordered tanglegram** on $(T,S)$ is a triple $(T,\phi,S)$ with $\phi: L(T) \to L(S)$ a bijection; an **unordered tanglegram** is a pair $(\{T,S\},\phi)$ in which the two trees are not ordered. A tree automorphism is determined by the permutation it induces on the leaves (Lemma 3); let $\mathrm{Aut}_L(T)$ denote the group of leaf permutations induced by automorphisms of $T$. Two tanglegrams $(T,\phi,S)$ and $(T,\phi',S)$ are **isomorphic** if there are $g \in \mathrm{Aut}_L(T)$ and $h \in \mathrm{Aut}_L(S)$ with $h \circ \phi = \phi' \circ g$ (Definition 4).

Identify $L(T)$ and $L(S)$ with $[n]$, so that $\phi$ becomes a permutation $w \in \mathfrak{S}_n$ and $\mathrm{Aut}_L(T), \mathrm{Aut}_L(S)$ become subgroups of $\mathfrak{S}_n$. Then (Proposition 14):

1. The tanglegrams isomorphic to $(T,w,S)$ correspond bijectively to the elements of the double coset $\mathrm{Aut}_L(S)\, w\, \mathrm{Aut}_L(T)$, so isomorphism classes of ordered tanglegrams on $(T,S)$ are the double cosets $\mathrm{Aut}_L(S)\backslash \mathfrak{S}_n / \mathrm{Aut}_L(T)$.
2. Isomorphism classes of unordered tanglegrams correspond to these double cosets with $H w K$ and $K w^{-1} H$ identified ($H = \mathrm{Aut}_L(S)$, $K = \mathrm{Aut}_L(T)$).

The number of bijections giving an ordered tanglegram isomorphic to $(T,w,S)$ is (Proposition 15)

$$
|\mathrm{Aut}_L(S)|\,\bigl[\mathrm{Aut}_L(T) : \mathrm{Aut}_L(T) \cap w^{-1}\mathrm{Aut}_L(S)\,w\bigr] = |\mathrm{Aut}_L(T)|\,\bigl[\mathrm{Aut}_L(S) : \mathrm{Aut}_L(S) \cap w\,\mathrm{Aut}_L(T)\,w^{-1}\bigr].
$$

The leaf automorphism groups themselves are computed recursively by Jordan's theorem: $\mathrm{Aut}_L$ of a rooted tree is a direct product of wreath products of the automorphism groups of its root subtrees with symmetric groups permuting isomorphic subtrees (Theorem 5), and an unrooted tree has the same automorphism group as the rooted tree obtained by rooting it at its unique centroid, or at a new node on the edge joining its two centroids (Theorem 10, Corollary 11).

## Expansion

An isomorphism replaces $w$ by $h w g^{-1}$ with $h \in \mathrm{Aut}_L(S)$ and $g \in \mathrm{Aut}_L(T)$, so isomorphism classes are exactly orbits of the two-sided action, that is, double cosets; swapping the two trees inverts the bijection, which gives the identification for unordered tanglegrams. The size of a double coset $H w K$ is $|H|\,[K : K \cap w^{-1} H w]$ by the orbit-stabilizer theorem, giving Proposition 15. The point of the reduction is that any question about pairs of leaf-labelled trees that is invariant under relabelling (a tree distance, a rearrangement count, a cophylogenetic score) is a function on tanglegrams, so distinct problems are indexed by double cosets rather than by all $n!$ labellings.

## Sources

- Frederick A. Matsen, Sara C. Billey, Arnold Kas, Matjaž Konvalinka, Tanglegrams: a reduction tool for mathematical phylogenetics, arXiv:1507.04784 (2015). <https://doi.org/10.48550/arXiv.1507.04784>. Published version: IEEE/ACM Transactions on Computational Biology and Bioinformatics 15(1) (2018), 343–349, <https://doi.org/10.1109/tcbb.2016.2613040>; locators above refer to the arXiv version.
