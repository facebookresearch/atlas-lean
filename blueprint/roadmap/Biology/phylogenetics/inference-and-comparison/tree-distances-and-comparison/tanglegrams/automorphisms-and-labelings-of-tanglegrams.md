# Automorphisms and labelings of tanglegrams

Let $Y$ be a tanglegram on trees $T$ and $S$ with $n$ leaves, given by a bijection $\phi: L(T) \to L(S)$, and let $\mathrm{Aut}_L(T)$ be the group of leaf permutations induced by automorphisms of $T$. An automorphism of an ordered tanglegram is an automorphism of the graph formed by the two trees and the between-leaf edges that maps each tree to itself; for an unordered tanglegram it may also exchange the two trees; for rooted tanglegrams roots are preserved. Let $\mathrm{Aut}_L(Y)$ be the induced group of permutations of $L(T)$ and set

$$
H = \mathrm{Aut}_L(T) \cap \phi^{-1}\,\mathrm{Aut}_L(T)\,\phi ,
$$

where, when $T$ and $S$ are isomorphic, $L(S)$ is identified with $L(T)$ through a fixed tree isomorphism.

1. If $Y$ is unordered, an automorphism exchanging the two trees exists if and only if $T \cong S$ and $\phi\,\mathrm{Aut}_L(T)\,\phi \cap \mathrm{Aut}_L(T) \neq \emptyset$ (Proposition 18).
2. If $Y$ is ordered, or $T \not\cong S$, then $\mathrm{Aut}_L(Y) = H$. If $Y$ is unordered and $T \cong S$, then $\mathrm{Aut}_L(Y)$ contains $H$ as a subgroup of index 2 when $\mathrm{Aut}_L(T) \cap \phi\,\mathrm{Aut}_L(T)\,\phi \neq \emptyset$, and equals $H$ otherwise (Proposition 19).
3. A labeled tanglegram is a tanglegram with a bijection from a label set $X$ of size $n$ to the leaves of one of its trees. The number of leaf-distinct labelings of a given $n$-tanglegram $Y$ is (Proposition 21)

$$
\frac{n!}{|\mathrm{Aut}_L(Y)|} .
$$

## Depends on

- [Tanglegram isomorphism classes as double cosets](tanglegram-isomorphism-classes-as-double-cosets.md)

## Expansion

An automorphism preserving both trees is a pair $(g,h)$ of tree automorphisms with $h \circ \phi = \phi \circ g$; since $h$ is determined by $g$, these correspond to the $g \in \mathrm{Aut}_L(T)$ with $\phi g \phi^{-1} \in \mathrm{Aut}_L(S)$, which is $H$ after identifying leaf sets. A tree-exchanging automorphism, when it exists, composes with these to form the nontrivial coset of $H$. The labeling count is orbit-stabilizer for the action of $\mathfrak{S}_n$ on labelings.

## Sources

- Frederick A. Matsen, Sara C. Billey, Arnold Kas, Matjaž Konvalinka, Tanglegrams: a reduction tool for mathematical phylogenetics, arXiv:1507.04784 (2015). <https://doi.org/10.48550/arXiv.1507.04784>. Published version: IEEE/ACM Transactions on Computational Biology and Bioinformatics 15(1) (2018), 343–349, <https://doi.org/10.1109/tcbb.2016.2613040>; locators above refer to the arXiv version.
