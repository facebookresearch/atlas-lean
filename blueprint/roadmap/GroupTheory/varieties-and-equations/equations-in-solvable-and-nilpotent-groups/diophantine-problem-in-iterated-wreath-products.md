# The Diophantine problem is undecidable in iterated wreath products of free abelian groups

For all $m, n \ge 1$, no algorithm decides whether a finite system of equations has a solution in the restricted wreath product $\mathbb{Z}^m \wr \mathbb{Z}^n$, and the same holds for every right-iterated wreath product of nontrivial free abelian groups of finite rank.

For groups $A$ and $B$, let $B \wr A$ be the restricted wreath product $\big(\bigoplus_{a \in A} B\big) \rtimes A$. For groups $A_1, \dots, A_k$ with $k \ge 2$, the right-iterated wreath product is defined by $\mathrm{IWP}_R(A_2, A_1) = A_2 \wr A_1$ and $\mathrm{IWP}_R(A_k, \dots, A_1) = A_k \wr \mathrm{IWP}_R(A_{k-1}, \dots, A_1)$. The *Diophantine problem* of a finitely generated group $G$ asks, given a finite system of equations with constants from $G$, whether it has a solution in $G$.

**Theorem (Kharlampovich and Miasnikov).**

1. For all $m, n \ge 1$, the Diophantine problem in $\mathbb{Z}^m \wr \mathbb{Z}^n$ is undecidable (Theorem 4.2 of arXiv:2502.09442v1).
2. If $A_1, \dots, A_k$, $k \ge 2$, are nontrivial free abelian groups of finite rank, then the Diophantine problem in $\mathrm{IWP}_R(A_k, \dots, A_1)$ is undecidable (Theorem 4.3).
3. If the Diophantine problem in a group $H$ is undecidable, then it is undecidable in $K \wr H$ whenever $K$ is abelian, and whenever $K$ is finite and $H$ is torsion-free (Theorem 3.1).

The case $m = n = 1$ of clause 1 is the undecidability of [systems of equations in $\mathbb{Z} \wr \mathbb{Z}$](systems-of-equations-undecidable-z-wr-z.md), first proved by Myasnikov and Romanovskii (stated as the undecidability of the universal theory with constants) and also by Dong, with a different argument. The source recalls that the full first-order theory of a finitely generated solvable group is decidable exactly when the group is virtually abelian (Ershov, Romanovskii, Noskov); the Diophantine problem concerns only finite systems of equations with constants.

## Depends on

- [Group](../../group-basics/group.md)
- [Restricted wreath product](../../soluble-finite-groups/solubility-nilpotency-and-subnormality/restricted-wreath.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Solution set of a system of equations](../equationally-noetherian-groups/solutions-2.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

For $G = \mathbb{Z}^m \wr \mathbb{Z}^n$ the source shows that several subgroups are definable by equations and that, for every polynomial $f$ with integer coefficients, the solutions of $f = 0$ in integers can be expressed by a finite system of equations in $G$ (Theorem 4.1); thus the ring $\mathbb{Z}$ is interpretable in $G$ by Diophantine formulas with coefficients (Corollary 3), and the Diophantine problem in $\mathbb{Z}$, undecidable by the Davis–Putnam–Robinson–Matiyasevich theorem, reduces to that of $G$. Clause 3 holds because the normal closure $N$ of $K$ in $K \wr H$ is the centralizer of a nontrivial element of $K$ when $K$ is abelian, hence definable by equations, so $H \cong (K \wr H)/N$ is interpretable by equations; clause 2 then follows from clause 1 by induction on $k$. The reduction from e-interpretability to the Diophantine problem is a lemma of Garreta, Miasnikov and Ovchinnikov quoted by the source; a complete expansion links it.

## Sources

- O. Kharlampovich and A. Miasnikov, "The Diophantine problem in iterated wreath products of free abelian groups is undecidable", *International Journal of Algebra and Computation*, 2026, pp. 1–14, doi:10.1142/S0218196726400096; read as arXiv:2502.09442v1, <https://arxiv.org/abs/2502.09442v1>: Theorems 3.1, 4.1, 4.2 and 4.3, Corollary 3, the definition of iterated wreath products in Section 4.3 and the introduction, in the numbering of arXiv:2502.09442v1.
