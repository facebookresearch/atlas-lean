# Trinets encode orchard networks

**Setting.** A **binary phylogenetic network** $\mathcal N$ on a finite set $X$ is a rooted acyclic digraph without parallel arcs whose root has in-degree 0 and out-degree 2, whose out-degree-0 vertices are exactly $X$ (each of in-degree 1), and whose other vertices are **tree vertices** (in-degree 1, out-degree 2) or **reticulations** (in-degree 2, out-degree 1). A pair $\{a,b\} \subseteq X$ with a common parent is a **cherry**; an ordered pair $(a,b)$ whose parents $p_a$ (a tree vertex) and $p_b$ (a reticulation) are joined by the arc $(p_a,p_b)$ is a **reticulated cherry**. *Reducing* $b$ in a cherry deletes $b$ and suppresses $p_a$; *cutting* $(a,b)$ deletes $(p_a,p_b)$ and suppresses $p_a$ and $p_b$. $\mathcal N$ is **orchard** if some sequence of these two operations reduces it to a single vertex; tree-child networks are orchard. For $A \subseteq X$, $\mathcal N_A$ is the network **exhibited** on $A$ (the full simplification of the union of all paths from the lowest stable ancestor of $A$ to $A$), and $Tn(\mathcal N) = \{\mathcal N_A : |A| = 3\}$ is its set of **trinets**. $\mathcal N$ is **recoverable** if the lowest stable ancestor of $X$ is the root, and a recoverable $\mathcal N$ is **encoded** by $Tn(\mathcal N)$ if every recoverable $\mathcal N'$ with $Tn(\mathcal N') = Tn(\mathcal N)$ is isomorphic to $\mathcal N$.

**Theorem (Theorem 1.3).** Let $\mathcal N$ be an orchard network on $X$ with $|X| \ge 3$ and vertex set $V$. Then
1. $Tn(\mathcal N)$ encodes $\mathcal N$, and
2. up to isomorphism, $\mathcal N$ can be reconstructed from $Tn(\mathcal N)$ in time $O(|V|^6)$.

In particular (Theorem 1.2) every tree-child network on at least three leaves is encoded by its trinets, and it can be rebuilt from them in polynomial time.

## Expansion

Orchard networks are recoverable (Lemma 3.1), and picking a cherry or reticulated cherry from an orchard network leaves an orchard network, in any order (Lemma 1.1). The trinets see the local structure that drives this reduction: $\{a,b\}$ is a cherry of $\mathcal N$ if and only if it is a cherry of every trinet $\mathcal N_A$ with $\{a,b\} \subseteq A$, and likewise for reticulated cherries (Lemma 3.3). After reducing or cutting, the trinets of the smaller network are computable from those of $\mathcal N$ (Lemmas 3.4–3.5), so induction on the length of a cherry-picking sequence proves encoding, and each step is a polynomial search over the trinet set. Unlike tree-child networks, orchard networks can have arbitrarily many vertices and arbitrarily high level for a fixed leaf set. The paper's final example exhibits two non-isomorphic recoverable level-4 networks with the same trinets, so the largest level at which all recoverable networks are trinet-encoded is at most 3. This generalizes the classical fact that a rooted binary tree is determined by its rooted triples.

## Sources

- Charles Semple and Gerry Toft, "Trinets encode orchard phylogenetic networks", arXiv:2012.02231 (2020), Section 1 (definitions), Lemma 1.1, Theorems 1.2–1.3, Lemmas 3.1 and 3.3–3.5, Section 5 (example), <https://doi.org/10.48550/arXiv.2012.02231>. Published version: Journal of Mathematical Biology 83 (2021) 28, <https://doi.org/10.1007/s00285-021-01654-7>.
