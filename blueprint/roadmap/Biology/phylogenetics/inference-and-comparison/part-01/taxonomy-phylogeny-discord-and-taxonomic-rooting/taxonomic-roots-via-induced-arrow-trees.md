# Taxonomic roots via induced arrow trees

**Setting.** A **rank function** on a leaf set $U$ is a map $\mathrm{rk}:2^U\to\mathbb N$ with $\max\{\mathrm{rk}(A),\mathrm{rk}(B)\}\le\mathrm{rk}(A\cup B)$; $\mathrm{rk}(A)$ is the rank of the most specific taxon containing all labels in $A$, and the inequality implies monotonicity under inclusion. For a node $x$ of an unrooted tree $T$, $\Psi(x;T)$ is the set of subtrees obtained by deleting $x$.

**Naive definition and its defect.** The subrank is $\mathrm{subrk}(x;T)=\max_{S\in\Psi(x;T)}\mathrm{rk}(S)$; $x$ is a *delicate* taxonomic root if it minimizes the subrank. If the tree is not convex at that rank (two disjoint subtrees each contain a pair of leaves whose rank equals the whole tree's), every internal node is a delicate root.

**Induced arrow tree.** At each internal node $x$, sort the ranks $r_1\le\dots\le r_m$ of the subtrees in $\Psi(x;T)$ and place an arrow $(x,y)$ towards the root $y$ of every subtree attaining the maximum rank $r_m$; leaves point to their neighbour. A node that is the origin of two or more arrows is a **multi arrow node (MAN)**; an edge carrying arrows in both directions is a **bi-arrow edge**.

**Results.**

- *Lemma 1 / Corollary 1.* If an arrow on edge $e_2$ points away from edge $e_1$, then $e_1$ carries an arrow pointing towards $e_2$.
- *Proposition 2.* If $x$ is a MAN, every node has an arrow pointing towards $x$.
- *Proposition 3.* The MANs form a convex (connected) set of nodes.
- *Proposition 4.* If there is no MAN, there is exactly one bi-arrow edge.
- *Definition 20.* The taxonomic roots are the MANs if any exist, otherwise the two endpoints of the bi-arrow edge.
- *Proposition 5.* Following arrows from any node reaches a taxonomic root in at most $\mathrm{diam}(T)$ steps.

## Expansion

An arrow from $x$ towards a subtree means that subtree contains the most taxonomically diverse part of the tree as seen from $x$. Monotonicity of the rank function makes arrows consistent along paths (Lemma 1), so all arrows not originating in the root set point towards it, which gives convexity of the MAN set, uniqueness of the bi-arrow edge in the MAN-free case, and the diameter bound for locating a root by walking.

## Sources

- F. A. Matsen, A. Gallagher, "Reconciling taxonomy and phylogenetic inference: formalism and algorithms for describing discord and inferring taxonomic roots", Algorithms for Molecular Biology 7:8 (2012), Definitions 13–20, Lemma 1, Corollary 1 and Propositions 2–5, <https://doi.org/10.1186/1748-7188-7-8>, PMCID: PMC3384453.
