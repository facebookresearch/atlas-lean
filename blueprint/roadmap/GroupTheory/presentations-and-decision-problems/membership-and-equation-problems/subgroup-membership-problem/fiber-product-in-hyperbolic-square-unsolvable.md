# A finitely presented subgroup of the square of a hyperbolic group can have unsolvable membership and conjugacy problems

There is a torsion-free word-hyperbolic group $\Gamma$ and a finitely presented subgroup $P \subseteq \Gamma \times \Gamma$ such that membership in $P$ is undecidable and $P$ has unsolvable conjugacy problem, although $\Gamma \times \Gamma$ is biautomatic with solvable conjugacy problem.

**Theorem (Baumslag–Bridson–Miller–Short).** There exist a torsion-free word-hyperbolic group $\Gamma$ and a finitely presented subgroup $P \subseteq \Gamma \times \Gamma$ such that there is no algorithm deciding membership in $P$, and the conjugacy problem for $P$ is unsolvable. One can arrange for $\Gamma$ to be the fundamental group of a compact negatively curved $2$-complex.

Conventions: membership refers to the fixed subgroup $P$ of the fixed group $\Gamma \times \Gamma$: given a word in the generators of $\Gamma \times \Gamma$, decide whether it lies in $P$. The ambient group $\Gamma \times \Gamma$, a direct product of hyperbolic groups, is biautomatic and has solvable conjugacy problem, so finitely presented subgroups of biautomatic groups need not inherit these properties. The source also shows that there is such a $P$ for which membership in its normalizer is undecidable.

## Depends on

- [Word-hyperbolic groups](../../../geometric-group-theory/hyperbolic-groups/is-hyperbolic.md)
- [Membership problem for a subset of a finitely generated group](../submonoid-and-rational-subset-membership/membership-problem-for-a-subset.md)
- [Solvable conjugacy problem for a quotient of a free group](../../decision-problems-in-free-abelianized-extensions/conjugacy-problem-solvable.md)
- [Group](../../../group-basics/group.md)

## Proof depends on

None.

## Expansion

Start from a finitely presented group $Q$ with a finite $2$-dimensional classifying space and unsolvable word problem, which exists by a theorem of Collins and Miller. An enhanced Rips construction gives a short exact sequence $1 \to N \to \Gamma \to Q \to 1$ with $\Gamma$ torsion-free hyperbolic and $N$ finitely generated. The fiber product $P = \{(\gamma, \gamma') : \gamma N = \gamma' N\} \subseteq \Gamma \times \Gamma$ is finitely presented by the 1-2-3 Theorem of the same paper, which has no page here. As in Mikhailova's construction for $F_2 \times F_2$ (see the [page on membership in F₂ × F₂](membership-problem-in-f2-times-f2-unsolvable.md)), a word $w$ in the generators of the first factor defines an element of $P$ exactly when it represents $1$ in $Q$, so membership in $P$ is undecidable, and an analysis of centralizers in $P$, using that centralizers of nontrivial elements of $\Gamma$ are cyclic, shows that its conjugacy problem is unsolvable. The Collins–Miller groups, the enhanced Rips construction and the 1-2-3 Theorem are the results a good expansion links; none has a page here.

## Sources

- Gilbert Baumslag, Martin R. Bridson, Charles F. Miller III and Hamish Short, *Fibre products, non-positive curvature, and decision problems*, Comment. Math. Helv. 75 (2000), no. 3, 457–477, https://doi.org/10.1007/s000140050136, read in the open-access publisher copy at https://ems.press/content/serial-article-files/42872: the statement is Theorem A of its introduction, with the remark on the solvable conjugacy problem of $\Gamma \times \Gamma$ after Theorem B, and the normalizer result is Corollary 5.2.
