# Phylogenetic networks are not encoded by their proper induced subnetworks

Use the definitions of [Induced subnetwork of a phylogenetic network](induced-subnetwork-of-a-phylogenetic-network.md). A class of networks is **encoded** by a family of building blocks if two networks in the class with the same blocks are equivalent. Rooted trees are encoded by their triplets, and level-2 and tree-child networks by their trinets; the result below shows that no such statement holds for arbitrary networks, even with all proper induced subnetworks as blocks.

**Construction.** Let $n \ge 3$, $X = \{x_1, \dots, x_n\}$ and $Y = \{y_1, \dots, y_n\}$ disjoint. Let $B_n$ be the binary words of length $n$, $B_n^1$ those of odd weight and $B_n^2$ those of even, nonzero weight, so $|B_n^1| = 2^{n-1}$ and $|B_n^2| = 2^{n-1} - 1$. For $i = 1, 2$ let $D_i$ be the rooted DAG on $X \cup Y \cup B_n^i \cup \{\rho_i\}$ with arcs

- $(\rho_i, u)$ for every $u \in B_n^i$,
- $(y_j, x_j)$ for $1 \le j \le n$,
- $(u, y_j)$ for $u \in B_n^i$ exactly when the $j$-th letter of $u$ is $1$,

and let $N_i$ be $D_i$ with its degenerate vertices suppressed. Both $N_1$ and $N_2$ are recoverable networks on $X$.

**Theorem (nonbinary counterexample).** For every $n \ge 3$, $N_1$ and $N_2$ are not equivalent, but they are network-equivalent: $N_1|_Y \cong N_2|_Y$ for every nonempty proper subset $Y \subsetneq X$.

**Theorem (binary counterexample).** For every $n \ge 3$ there are binary phylogenetic networks $H_1, H_2$ on $X$, obtained from $D_1, D_2$ by replacing the root star with a binary tree on $B_n^i$, each in-star of $y_j$ with a binary tree, and each high-outdegree vertex $u$ with a rooted caterpillar on its children, that are not equivalent but are network-equivalent.

In particular, for every taxon set of size at least $3$ there are inequivalent networks with exactly the same trinets; the supplementary material shows they also display the same trees. A method that outputs a network from all of its proper subnetworks, or from all displayed trees, can therefore return an incorrect history. The examples have level exponential in $|X|$, so encoding of networks of low level (for example, linear in $|X|$) is left open.

## Depends on

- [Induced subnetwork of a phylogenetic network](induced-subnetwork-of-a-phylogenetic-network.md)

## Expansion

*Inequivalence.* $B_n^1 \cap B_n^2 = \emptyset$ and the all-ones word $1^n$ lies in exactly one of them, so exactly one of $N_1$, $N_2$ has a child of the root with outdegree $n$.

*Network-equivalence.* By the lemma on recoverable networks it suffices to treat $Y = X \setminus \{x_k\}$. Restricting $D_i$ to arcs on root-to-$X_k$ paths deletes $x_k$, $y_k$ and, in $D_1$, the unit word $w_k = e_k$, whose only child was $y_k$; in $D_2$ every word keeps a child $y_j$ with $j \ne k$ because its weight is at least $2$. Let $\phi_k$ flip the $k$-th letter. It changes parity and sends $e_k$ to $0^n$, so it restricts to a bijection $B_n^1 \setminus \{e_k\} \to B_n^2$. Extending it by the identity on $X_k \cup Y_k$ and the roots gives an isomorphism of the restricted DAGs, since for $j \ne k$ the $j$-th letters of $u$ and $\phi_k(u)$ agree, so $(u, y_j)$ is an arc exactly when $(\phi_k(u), y_j)$ is. Suppressing degenerate vertices in isomorphic DAGs gives equivalent networks. The binary case follows the same flip argument with lemmas showing that the inserted caterpillars and trees restrict isomorphically under $\phi_k$.

## Sources

- K. T. Huber, L. van Iersel, V. Moulton and T. Wu, "How much information is needed to infer reticulate evolutionary histories?", Systematic Biology 64(1) (2015), 102–111, Binary Sequences, Nonbinary Network Examples (Theorem 1), Binary Network Examples (Theorem 2), Discussion and Appendix (Lemmas 2–3), <https://doi.org/10.1093/sysbio/syu076> (PMC4265143).
- L. van Iersel and V. Moulton, "Trinets encode tree-child and level-2 phylogenetic networks", Journal of Mathematical Biology 68 (2014), 1707–1729, <https://doi.org/10.1007/s00285-013-0683-5>.
