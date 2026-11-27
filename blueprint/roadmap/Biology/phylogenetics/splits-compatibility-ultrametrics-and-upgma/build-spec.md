# Correctness of BUILD

Let $S$ be a nonempty finite set and $R$ a finite set of [triplets](triplet.md) $xy \mid z$ with $x, y, z \in S$ and $z \ne x$ or $z \ne y$. Then some [binary hierarchy](../../../Combinatorics/elementary-enumeration/counting-binary-phylogenetic-trees/is-binary-hierarchy.md) on $S$ [displays](displays-triplet.md) every triplet of $R$ if and only if, for every $S' \subseteq S$ with $|S'| \ge 2$, the Aho graph of $R$ on $S'$ [has a cut](has-aho-cut.md) (Aho, Sagiv, Szymanski & Ullman 1981; Semple & Steel 2003).

## Sources

- A. V. Aho, Y. Sagiv, T. G. Szymanski and J. D. Ullman, *Inferring a tree from lowest common ancestors with an application to the optimization of relational expressions*, SIAM J. Comput. 10 (1981), 405–421.
- C. Semple and M. Steel, *Phylogenetics*, Oxford University Press (2003).
