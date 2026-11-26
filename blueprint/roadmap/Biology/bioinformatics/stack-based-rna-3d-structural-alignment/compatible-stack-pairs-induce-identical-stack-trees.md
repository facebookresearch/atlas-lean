# Compatible stack pairs induce identical stack trees

**Stacks.** In a pseudoknot-free secondary structure, a helix of $l \ge k$ nested base pairs splits into $l - k + 1$ overlapping $k$-stacks. Given two RNAs $A$ and $B$, a $k$-stack of $A$ and one of $B$ are 3D-conserved when the RMSD of their backbone coordinates after optimal (Kabsch) superposition is below a cutoff $r_c$; diagonal runs of conserved $k$-stack pairs are merged into maximal **e-stack pairs** $s_i = (q_i^A, q_i^B)$.

**Relations and tree model.** Two non-overlapping stacks $q, q'$ of one structure are related either by enclosure ($q \prec_E q'$, $q$ encloses $q'$) or by juxtaposition ($q \prec_J q'$, $q$ lies before $q'$); both are strict partial orders. The non-overlapping stacks of a structure form an ordered tree: a pseudo stack is the root, each stack is a child of the stack that directly encloses it, and siblings are ordered by $\prec_J$. Two e-stack pairs $s_i, s_j$ are **compatible** if $q_i^A \, R \, q_j^A$ and $q_i^B \, R \, q_j^B$ hold for the same relation $R \in \{\prec_E, \succ_E, \prec_J, \succ_J\}$.

**Lemma 1.** For a non-empty set of e-stack pairs in which every two pairs are compatible, the corresponding sets of e-stacks of $A$ and of $B$ have the same ordered tree structure.

**Consequence.** Build the compatibility graph whose vertices are e-stack pairs, with an edge when two pairs are compatible and also share a similar rigid transformation (the RMSD of their concatenated coordinates is below the cutoff). Any clique is a consistent consensus of stacks with isomorphic trees in the two molecules; a maximum clique is taken as the conserved helical core. The core splits the remaining sequence into matched hairpin, internal and multi-loops, which are aligned pairwise by an affine-gap dynamic program using the superposition of the core.

## Expansion

The proof is by induction on tree depth. If a stack $q_j^A$ were a child of $q_i^A$ while $q_j^B$ were not a child of $q_i^B$, then $q_j^B$ would lie in the subtree of some child of $q_i^B$, so it would have more enclosing stacks than its partner, and some pair of e-stack pairs would disagree on enclosure, contradicting pairwise compatibility. Hence children correspond to children, and their order agrees because juxtaposition is also preserved. Pairwise compatibility therefore guarantees a globally consistent, order-preserving correspondence of helices, which is why a clique (a pairwise condition) suffices.

## Sources

- P. Ge, S. Zhang, "STAR3D: a stack-based RNA 3D structural alignment tool", Nucleic Acids Research 43(20) (2015) e137, Materials and Methods (k-stacks, e-stacks, tree model of stacks, Lemma 1, compatible graph, loop alignment), <https://doi.org/10.1093/nar/gkv697> (PMC4787758).
