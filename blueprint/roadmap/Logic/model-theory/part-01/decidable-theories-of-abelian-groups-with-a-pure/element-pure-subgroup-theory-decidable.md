# Kourovka Problem 3.21(a): element-pure-subgroup theory of abelian groups

Statement (Kourovka Notebook Problem 3.21(a), A. I. Kokorin): the element-pure-subgroup theory of abelian groups is decidable. This is the elementary theory of the two-sorted structures $(A, \text{pure subgroups of } A)$, for $A$ an abelian group, with the group operations on elements, membership $\in$ of elements in subgroups, and inclusion $\subseteq$ of subgroups. Precisely, the set of coded two-sorted prenex sentences $s$ that hold in $(A, \text{pure subgroups of } A)$ for every abelian group $A$ is a computable set of codes.

A subgroup $B$ of an abelian group $A$ is pure if $nA \cap B = nB$ for every integer $n$, that is, whenever $na \in B$ with $n \in \mathbb{Z}$ and $a \in A$, there is $b \in B$ with $nb = na$. Every two-sorted sentence is effectively equivalent to such a prenex code, so decidability does not depend on the coding. It is false; the refutation is [Undecidability of the element-pure-subgroup theory of abelian groups](element-pure-subgroup-theory-decidable-r.md).

## Sources

- E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.21 (A. I. Kokorin), https://arxiv.org/abs/1401.0300v49.
