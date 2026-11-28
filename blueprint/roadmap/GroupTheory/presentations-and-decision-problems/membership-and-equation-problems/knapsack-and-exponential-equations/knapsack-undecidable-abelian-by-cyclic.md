# Knapsack is undecidable in some finitely generated abelian-by-cyclic group

There is a finitely generated abelian-by-cyclic group $\mathcal{A} \rtimes \mathbb{Z}$ with fixed elements $g_1, \dots, g_m$ such that no algorithm decides, given $g$, whether $g_1^{z_1} \cdots g_m^{z_m} = g$ for some $z_i \in \mathbb{N}$; so its knapsack problem is undecidable.

There exist a finitely generated abelian-by-cyclic group $\mathcal{A} \rtimes \mathbb{Z}$ and elements $g_1, \dots, g_m$ of it such that it is undecidable, given $g \in \mathcal{A} \rtimes \mathbb{Z}$, whether there exist $z_1, \dots, z_m \in \mathbb{N}$ with $g_1^{z_1} g_2^{z_2} \cdots g_m^{z_m} = g$ (Theorem 1.5 of the source). In particular the knapsack problem is undecidable in this group. Mishchenko and Treier gave an earlier example; the source gives a different and more direct proof.

By contrast, coset intersection is decidable in all finitely generated abelian-by-cyclic groups (Theorem 1.6), and knapsack is decidable in $G \wr \mathbb{Z}$ for non-trivial finitely generated abelian $G$ (Ganardi, König, Lohrey and Zetzsche, as the introduction of the source recalls).

## Depends on

- [Knapsack problem for a finitely generated group](knapsack-problem-for-a-group.md)
- [Group](../../../group-basics/group.md)
- [Abelian group](../../../group-basics/abelian-group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The key result is that there are $n$, a finitely presented $\mathbb{Z}[X^{\pm}]$-module $\mathcal{A}$ and fixed elements $f_1, \dots, f_n \in \mathcal{A}$ such that it is undecidable, given $f_0$, whether $X^{z_1} f_1 + \cdots + X^{z_n} f_n = f_0$ for some $z_i \in \mathbb{Z}$ (Theorem 1.1), proved from Hilbert's tenth problem by encoding integer variables through monomials modulo powers of $X - 1$. In $\mathcal{A} \rtimes \mathbb{Z}$, with $\mathbb{Z}$ acting by multiplication by $X$, products of powers of fixed elements produce such monomial combinations. For $n = 1$ the equation is decidable by Noskov's lemma (Theorem 1.2).

## Sources

- R. Dong, "Linear equations with monomial constraints and decision problems in abelian-by-cyclic groups", in Proceedings of the 2025 Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 2025), SIAM (2025), 1892–1908, https://doi.org/10.1137/1.9781611978322.59; read in arXiv:2406.08480v3, whose numbering is used here (Theorems 1.1, 1.2, 1.5 and 1.6 of arXiv:2406.08480v3).
