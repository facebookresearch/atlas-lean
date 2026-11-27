# Rooted phylogenetic trees correspond to set partitions with blocks of size at least two

**Objects.** A rooted phylogenetic tree on $[n] = \{1,\dots,n\}$ is a rooted tree whose leaves are labelled by $[n]$ and whose internal (non-leaf) vertices each have at least two children; $\mathcal{RP}_n$ is the set of such trees. Binary trees are those whose internal vertices have exactly two children.

**Labelling (Erdős–Székely, Diaconis–Holmes).** Given $T \in \mathcal{RP}_n$, label internal vertices one at a time: among unlabelled non-root internal vertices whose children are all labelled, pick the one whose children carry the lowest label and give it the next label $n+1, n+2, \dots$. A tree with $\ell$ internal vertices thus has its $m = \ell - 1$ non-root internal vertices labelled $n+1,\dots,n+m$; the root stays unlabelled.

**Theorem.** Mapping $T$ to the set partition of $[n+m]$ whose blocks are the sibling sets (the children of each internal vertex) is a bijection between non-trivial rooted phylogenetic trees and partitions of finite sets $[t]$ into blocks of size at least $2$. A partition $\pi$ of $[t]$ with $\ell(\pi)$ blocks corresponds to a tree on

$$n = t - \ell(\pi) + 1$$

leaves, with $m = \ell(\pi) - 1$ non-root internal vertices. Consequently $\mathcal{RP}_n$ is in bijection with the partition diagrams $\mathcal D^{(\ge2)}_{[n]}$ built from such partitions, and trees with $n$ leaves and $m$ non-root internal vertices are counted by partitions of $[n+m]$ into $m+1$ blocks of size $\ge 2$ (partial Bell polynomials).

For binary trees every block has size $2$, recovering the Diaconis–Holmes bijection between rooted binary trees on $n$ leaves and perfect matchings of $[2n-2]$, so $|\mathcal{RP}^{\mathrm{bin}}_n| = (2n-3)!!$. Allowing singleton blocks (labelled roots) extends the bijection to forests: the set of all forests is in bijection with the set of all partitions of finite sets, and forests on $n$ leaves with the partitions $\Lambda_{[n]}$.

## Proof sketch

The labelling is canonical, so a tree determines its partition. Conversely, given a partition of $[t]$ with blocks of size $\ge 2$, set $n = t - \ell + 1$ and rerun the labelling rule on blocks: among unassigned blocks all of whose elements are already available labels (initially $[n]$), the one containing the lowest label is the child set of the next label $n+1, n+2, \dots$; the last remaining block is the root's child set. This inverts the forward map. The count identity $t = n + m$ and $\ell = m + 1$ gives $n = t - \ell + 1$. Encoding the same data as diagrams in the Brauer category, with $n$ upper and $n-2$ lower points for binary trees, lets tree sets inherit semigroup structures from diagram composition; for example, the symmetric group $S_n$ acts on the left by permuting leaf labels, and Green's relations of the resulting semigroups organize trees into classes.

## Sources

- Andrew Francis and Peter D. Jarvis, "Brauer and partition diagram models for phylogenetic trees and forests", *Proceedings of the Royal Society A: Mathematical, Physical and Engineering Sciences* 478 (2022), 20220044, <https://doi.org/10.1098/rspa.2022.0044>. Preprint version: arXiv:2111.15225 (2021), internal vertex labelling algorithm, theorem on trees and partitions with blocks of size at least two, its corollary for fixed $n$, and the forest–partition theorem, <https://doi.org/10.48550/arXiv.2111.15225>.
