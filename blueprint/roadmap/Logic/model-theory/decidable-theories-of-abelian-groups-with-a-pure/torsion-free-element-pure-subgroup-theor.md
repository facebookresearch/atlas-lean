# Kourovka Problem 3.21(b): pure-subgroup theory of torsion-free abelian groups

Statement (Kourovka Notebook Problem 3.21(b), A. I. Kokorin): the element-pure-subgroup theory of torsion-free abelian groups is decidable. Precisely, the set of coded two-sorted prenex sentences $s$ that hold in $(A, \text{pure subgroups of } A)$ for every abelian group $A$ that is torsion-free (for all $n \in \mathbb{N}$ with $n \neq 0$ and all $a \in A$, $na = 0$ implies $a = 0$) is a computable set of codes. The language has the group operations on elements, membership $\in$ of elements in subgroups, and inclusion $\subseteq$ of subgroups, and subgroup quantifiers range over pure subgroups.

A subgroup $B$ of an abelian group $A$ is pure if $nA \cap B = nB$ for every integer $n$, that is, whenever $na \in B$ with $n \in \mathbb{Z}$ and $a \in A$, there is $b \in B$ with $nb = na$. It is false; the refutation is [Undecidability of the pure-subgroup theory of torsion-free abelian groups](torsion-free-element-pure-subgroup-theor-2.md).

## Sources

- E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.21 (A. I. Kokorin), https://arxiv.org/abs/1401.0300v49.
