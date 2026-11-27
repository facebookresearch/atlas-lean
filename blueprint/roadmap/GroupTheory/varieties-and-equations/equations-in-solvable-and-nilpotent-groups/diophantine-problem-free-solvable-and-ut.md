# The Diophantine problem is undecidable in free solvable groups, UT(n, Z) and SL(3, Z)

No algorithm decides solvability of finite systems of equations in a finitely generated non-abelian free solvable group, in the unitriangular groups $UT(n, \mathbb{Z})$ for $n \geq 3$, in $GL(3, \mathbb{Z})$, $SL(3, \mathbb{Z})$ and $T(3, \mathbb{Z})$, or in a finitely generated nilpotent group whose $G'/\gamma_3(G)$ has rank 1 or 2.

For a finitely generated group $G$, the *Diophantine problem* $\mathcal{D}(G)$ asks, given a finite system of equations in variables with constants from $G$ (constants written as words in a fixed finite generating set), whether the system has a solution in $G$. Here $UT(n, \mathbb{Z})$ is the group of upper unitriangular $n \times n$ integer matrices, $T(3, \mathbb{Z})$ the group of invertible upper triangular $3 \times 3$ integer matrices, $\gamma_i(G)$ the lower central series and $G' = \gamma_2(G)$.

**Theorem (Garreta, Miasnikov and Ovchinnikov).** In each of the following groups $G$ the ring $\mathbb{Z}$ is interpretable by finite systems of equations, and $\mathcal{D}(G)$ is undecidable:

1. $G = UT(n, \mathbb{Z})$ for every $n \geq 3$ (Theorem 4.9 of arXiv:1805.04085v2);
2. every finitely generated nilpotent group $G$ such that the abelian group $G'/\gamma_3(G)$ has rank $1$ or $2$ (Proposition 4.11 of arXiv:1805.04085v2);
3. every finitely generated non-abelian free solvable group (Theorem 4.33 of arXiv:1805.04085v2), and more generally every non-abelian free (solvable-by-nilpotent) group, a relatively free group in a product variety $\mathcal{A}^d\mathcal{N}_c$ (Theorem 4.34 of arXiv:1805.04085v2).

Moreover $\mathcal{D}(G)$ is undecidable for $G = GL(3, \mathbb{Z})$, $SL(3, \mathbb{Z})$ and $T(3, \mathbb{Z})$ (Example 4.30 of arXiv:1805.04085v2).

The same paper proves undecidability for every finitely generated non-abelian free nilpotent group (Theorem 4.7), which is also the subject of [Systems of equations are undecidable in every non-abelian free nilpotent group](systems-of-equations-undecidable-free-nilpotent.md). Part 3 extends Roman'kov's theorem that finitely generated non-abelian free metabelian groups have undecidable Diophantine problem. For an arbitrary finitely generated nilpotent group that is not virtually abelian, the source only shows that $\mathcal{D}(O)$ reduces to $\mathcal{D}(G)$ for some ring of algebraic integers $O$, so undecidability there would follow from the conjectured undecidability of $\mathcal{D}(O)$; virtually abelian groups have decidable Diophantine problem.

## Depends on

- [Group](../../group-basics/group.md)
- [Commutator subgroup of a group](../../commutators-and-engel-conditions/commutator-subgroup.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

All cases interpret the ring $\mathbb{Z}$ in $G$ by finite systems of equations (an e-interpretation), so the Diophantine problem of $\mathbb{Z}$, undecidable by Matiyasevich's theorem, reduces to $\mathcal{D}(G)$. For a nilpotent group of class 2, $\mathbb{Z}$ arises as the largest ring of scalars of the commutator map $G/Z(G) \times G/Z(G) \to G'$, which is e-interpretable and equals $\mathbb{Z}$ when $G$ has a centralizer-small element; for higher class one passes to the quotient $G/\gamma_3(G)$ when $\gamma_3(G)$ is e-definable. Free solvable groups are handled by induction on the derived length, starting from free metabelian groups, which are verbally elliptic so that $G/\gamma_3(G)$ is e-interpretable. For $GL(3, \mathbb{Z})$, $SL(3, \mathbb{Z})$ and $T(3, \mathbb{Z})$, the subgroup $Z(G)\,UT(3, \mathbb{Z})$ is a maximal 2-nilpotent subgroup and therefore e-definable, which reduces to the case of $UT(3, \mathbb{Z})$. A complete expansion links pages for the e-interpretability of the largest ring of scalars of a bilinear map and for the verbal ellipticity of free metabelian groups, which have none.

## Sources

- A. Garreta, A. Miasnikov and D. Ovchinnikov, "Diophantine problems in solvable groups", *Bulletin of Mathematical Sciences* 10(1), 2020, article 2050005, doi:10.1142/S1664360720500058; read as arXiv:1805.04085v2, <https://arxiv.org/abs/1805.04085v2>: Theorems 4.7, 4.9, 4.33 and 4.34, Proposition 4.11, Example 4.30 and the introduction, with the numbering of that version.
