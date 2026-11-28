# Designability of P-unsaturated floral trees

**Setting.** A pseudoknot-free secondary structure on positions $\{1,\dots,n\}$ is a set of arcs $\{i,j\}$, $i<j$, with no shared endpoints and no crossing pair $i<k<j<\ell$. For an RNA sequence, a *maximum-size arc set* is a secondary structure with the largest number of arcs, allowing only $\{G,C\}$ and $\{A,U\}$ pairs. A sequence is a **design** if its maximum-size arc set is unique, and a structure $R$ is **designable** if some design has $R$ as its unique maximum-size arc set (the combinatorial RNA design problem). Assuming positions $1$ and $n$ pair, $R$ corresponds to a rooted tree: each base pair is a two-dot vertex, each unpaired base a one-dot leaf, and the children of a pair are the elements nested directly beneath it. The tree is *saturated* if every leaf has two dots.

**Known results (Haleš et al.).** A saturated tree is designable iff its root has at most four children and every other vertex at most three; an unsaturated tree with a vertex having at least two two-dot children and at least one one-dot child is not designable.

**Definitions.** A rooted tree is *P-unsaturated* if every leaf at maximum depth has exactly one dot and every other vertex has two dots. It is *floral* (resp. *perfect floral*) if deleting all vertices at maximum depth leaves a binary tree (resp. a perfect binary tree). The *natural labelling* of a P-unsaturated perfect floral tree of height $n+1$ labels depth-$(n+1)$ vertices A if $n+1$ is even and C if odd, labels the other vertices at even depths alternately AU, UA from left to right, and those at odd depths alternately GC, CG.

**Theorem.**
1. The secondary structure of a P-unsaturated perfect floral tree is designable, and the sequence read off from its natural labelling is a design.
2. The secondary structure of any P-unsaturated floral tree is designable, with a design given by the labelled subtree of the natural labelling of a perfect floral tree.
3. The same holds in the model where wobble $\{G,U\}$ pairs are also allowed, i.e. energy minimization is equivalent to maximizing the number of $\{G,C\}$, $\{A,U\}$ and $\{G,U\}$ pairs.

## Expansion

These trees have unpaired nucleotides only at the greatest depth, so they avoid the non-designable configuration of a vertex with both two-dot and one-dot children, and they extend the saturated classification to an infinite unsaturated family. The proof is constructive: one shows that the natural labelling admits no maximum-size arc set other than the target. The labelling alternates pair orientation between siblings (AU versus UA, GC versus CG) and pair type between depths, and uses a single base for all unpaired leaves, which limits the arcs any competing structure can form; the proof checks that every competitor has strictly fewer arcs. Pruning a perfect floral tree to a floral subtree, and adding wobble pairs, preserve this uniqueness.

## Sources

- Jonathan Jedwab, Tara Petrie and Samuel Simon, "An infinite class of unsaturated rooted trees corresponding to designable RNA secondary structures", arXiv:1709.08088 (2017), Section 2 (Theorems 2.4-2.6) and Section 3 (Definitions, Theorem 3.3, Corollaries 3.4 and 3.5), <https://doi.org/10.48550/arXiv.1709.08088>.
