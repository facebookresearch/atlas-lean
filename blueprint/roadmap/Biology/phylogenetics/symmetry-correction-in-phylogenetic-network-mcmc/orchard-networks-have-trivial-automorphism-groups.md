# Orchard networks have trivial automorphism groups

**Setting.** A rooted phylogenetic network $N$ is a rooted DAG whose leaves are bijectively labelled; an automorphism of $N$ is a digraph automorphism that fixes every leaf. The *$\mu$-vector* of a vertex $v$ lists, for each leaf $x$, the number of directed paths from $v$ to $x$; for a vertex $v$ with children $c_1,\dots,c_k$,

$$\mu(v)=\sum_{i=1}^k\mu(c_i).$$

$N$ is *orchard* if it reduces to a single leaf by repeatedly reducing cherries (deleting one leaf of a sibling pair) and reticulated cherries (deleting the reticulation edge between the two leaves' parents).

**Theorem.** If $N$ is a leaf-labelled orchard network, then $|\mathrm{Aut}(N)|=1$.

**Proposition (tree clone-free networks).** If no two distinct tree vertices of $N$ have the same $\mu$-vector, then $|\mathrm{Aut}(N)|=1$.

**Corollary.** Leaf-labelled tree-child networks and leaf-labelled trees have trivial automorphism groups (tree-child networks are orchard).

Consequently, Metropolis–Hastings samplers restricted to orchard, tree-child or tree space need no symmetry correction: the factor $|\mathrm{Aut}(N')|/|\mathrm{Aut}(N)|$ in the acceptance probability is $1$.

## Expansion

Automorphisms fix leaves and preserve $\mu$-vectors, so tree vertices can only be mapped to tree vertices with the same $\mu$-vector. Two distinct tree vertices with equal $\mu$-vectors are *tree clones*; in a tree clone-free network every tree vertex is therefore fixed. If some reticulation $r_1$ were moved, choose a highest one; its parents are fixed tree vertices $t_1,t_2$, so its image $r_2$ has the same parents, and the recursion gives $\mu(t_1)=\mu(r_1)+\mu(r_2)=\mu(t_2)$, making $t_1,t_2$ tree clones, a contradiction. Orchard networks are tree clone-free, which gives the theorem.

## Depends on

- [Automorphism-corrected Metropolis–Hastings for leaf-labelled networks](automorphism-corrected-metropolis-hastings-for-leaf-labelled-networks.md)

## Sources

- Leo van Iersel, Remie Janssen, Mark Jones, Yukihiro Murakami, "Metropolis-Hastings Sampling of Phylogenetic Networks: Correcting for Symmetries", arXiv:2608.12430: Lemma 5 ($\mu$-vector recursion), Proposition 1 (tree clone-free networks), Theorem 4 (orchard networks), Corollaries 2–3 (tree-child networks and trees). <https://doi.org/10.48550/arXiv.2608.12430>
