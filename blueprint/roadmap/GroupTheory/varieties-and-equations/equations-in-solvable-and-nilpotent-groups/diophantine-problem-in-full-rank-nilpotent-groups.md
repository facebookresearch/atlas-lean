# The Diophantine problem is undecidable in nilpotent groups of full-rank deficiency at least two

In a finitely generated nilpotent group of class at least two given by a full-rank presentation of deficiency at least two, and in every finitely generated 2-step nilpotent group with a centralizer-small element, no algorithm decides whether a finite system of equations has a solution.

For a group $G$, the *Diophantine problem* $\mathcal{D}(G)$ asks, given a finite system of equations in variables with constants from $G$ (written as words in a fixed finite generating set), whether the system has a solution in $G$. Let $\mathcal{N}_c$ be the variety of nilpotent groups of class at most $c$. A presentation $G = \langle a_1, \dots, a_n \mid r_1, \dots, r_m \rangle_{\mathcal{N}_c}$ in $\mathcal{N}_c$ has *relation matrix* $M(A, R)$, the $m \times n$ integer matrix whose $(i, j)$ entry is the exponent sum of $a_j$ in $r_i$; the presentation has *full rank* if $M(A, R)$ has rank $\min(m, n)$, and its *deficiency* is $n - m$. An element $g$ of $G$ is *centralizer-small* if its centralizer is $C_G(g) = \{g^t z : t \in \mathbb{Z},\ z \in Z(G)\}$ and $C_G(g)/Z(G)$ is infinite cyclic. A *$\tau_2$-group* is a finitely generated, torsion-free, 2-step nilpotent group.

**Theorem (Garreta, Miasnikov and Ovchinnikov).**

1. If $G$ is a finitely generated 2-step nilpotent group with a centralizer-small element, then the ring $\mathbb{Z}$ is interpretable in $G$ by finite systems of equations, and $\mathcal{D}(G)$ is undecidable (Theorem 3.5 of arXiv:1612.01242v4).
2. Let $G$ be a nilpotent group given in $\mathcal{N}_c$, $c \ge 2$, by a finite full-rank presentation of deficiency $d$. If $d \ge 2$, then $\mathbb{Z}$ is interpretable in $G$ by finite systems of equations and $\mathcal{D}(G)$ is undecidable; if $d \le 1$, then $\mathcal{D}(G)$ is decidable (Theorem 4.14 of arXiv:1612.01242v4).
3. Fix $n, m$ with $m \ge n - 1 \ge 1$, and choose a $\tau_2$-group $G = \langle a_1, \dots, a_n, c_1, \dots, c_m \mid [a_i, a_j] = \prod_t c_t^{\lambda_{t,i,j}},\ [A, C] = [C, C] = 1 \rangle$ by choosing the integers $\lambda_{t,i,j}$ uniformly with $|\lambda_{t,i,j}| \le \ell$. Then, asymptotically almost surely as $\ell \to \infty$, $\mathbb{Z}$ is definable in $G$ by finite systems of equations and $\mathcal{D}(G)$ is undecidable (Theorem 4.8 of arXiv:1612.02651v1).

Clause 1 recovers the undecidability of the Diophantine problem in every non-abelian free nilpotent group (Corollary 3.6 of arXiv:1612.01242v4), which is also stated in [Systems of equations are undecidable in every non-abelian free nilpotent group](systems-of-equations-undecidable-free-nilpotent.md). For finitely generated abelian groups the Diophantine problem is decidable.

## Depends on

- [Group](../../group-basics/group.md)
- [Center of a group](../../group-basics/group-center.md)
- [Centralizer subgroups](../../subgroup-embedding/lattices-of-centralizers/is-centralizer.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Solution set of a system of equations](../equationally-noetherian-groups/solutions-2.md)
- [Varieties of groups](../axiomatizable-classes-of-groups/is-variety.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

If a structure $\mathcal{A}$ is interpretable in $\mathcal{M}$ by finite systems of equations, then $\mathcal{D}(\mathcal{A})$ reduces to $\mathcal{D}(\mathcal{M})$ (Corollary 2.10 of arXiv:1612.01242v4), and $\mathcal{D}(\mathbb{Z})$ is undecidable by the Davis–Putnam–Robinson–Matiyasevich theorem. In a finitely generated 2-step nilpotent group with a centralizer-small element, the largest ring of scalars of the commutator map is $\mathbb{Z}$ (Theorem 3.4), and it is interpretable by equations, which gives clause 1. For a full-rank presentation in $\mathcal{N}_c$ of deficiency $d \ge 2$, a subset of $d$ generators generates a free $c$-step nilpotent subgroup of finite index (Theorem 4.1); the 2-nilpotent quotient $G/\gamma_3(G)$ is interpretable by equations and has centralizer-small elements, which gives clause 2. For random $\tau_2$-groups all the $a_k$ are centralizer-small and pairwise non-commuting asymptotically almost surely, and $\mathbb{Z}$ is definable by equations whenever two non-commuting centralizer-small elements exist (Theorem 3.2 of arXiv:1612.02651v1). For deficiency $d \le 1$ the same structure theorem makes $G$ virtually abelian, and the source invokes Ershov's theorem that finitely generated virtually abelian groups have decidable Diophantine problem. A complete expansion links Ershov's theorem.

## Sources

- A. Garreta, A. Miasnikov and D. Ovchinnikov, "Full rank presentations and nilpotent groups: structure, Diophantine problem, and genericity", *Journal of Algebra* 556 (2020), 1–34, doi:10.1016/j.jalgebra.2020.01.030; read as arXiv:1612.01242v4, <https://arxiv.org/abs/1612.01242v4>: Theorems 3.4, 3.5, 4.1 and 4.14, Corollaries 2.10 and 3.6, and the definitions of the introduction, in the numbering of arXiv:1612.01242v4 (clauses 1 and 2).
- A. Garreta, A. Miasnikov and D. Ovchinnikov, "Random nilpotent groups, polycyclic presentations, and Diophantine problems", *Groups Complexity Cryptology*, 2017, doi:10.1515/gcc-2017-0007; read as arXiv:1612.02651v1, <https://arxiv.org/abs/1612.02651v1>: Theorems 3.2 and 4.8, the definition of $\tau_2$-groups in Section 2 and the model $\mathcal{P}(n, m, \ell)$ of Section 4.2, in the numbering of arXiv:1612.02651v1 (clause 3).
