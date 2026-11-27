# Knapsack is undecidable for class-two nilpotent groups with large derived subgroup

If $G$ is a torsion-free nilpotent group of class 2 whose derived subgroup has rank greater than 322, then the knapsack problem for $G$ is undecidable; this covers the free nilpotent groups of class 2 and rank at least 26, and the groups $\mathrm{UT}_n(\mathbb{Z})$, $\mathrm{GL}_n(\mathbb{Z})$, $\mathrm{SL}_n(\mathbb{Z})$ for $n \ge 53$.

The knapsack problem here is the integer version: given words $g_1, \dots, g_k, g$ in the generators of $G$, decide whether $g_1^{\varepsilon_1} \cdots g_k^{\varepsilon_k} = g$ for some integers $\varepsilon_1, \dots, \varepsilon_k$. For a group $G$ let $\operatorname{rank}([G, G])$ be the torsion-free rank of its derived subgroup. Then (source):

1. if $G$ is a finitely generated torsion-free nilpotent group of class 2 with $\operatorname{rank}([G, G]) > 322$, the knapsack problem for $G$ is undecidable (Theorem 1);
2. if $G$ is the free nilpotent group of class 2 on $n \ge 26$ generators, the knapsack problem for $G$ is undecidable (Corollary 1);
3. for $n \ge 53$ the knapsack problem is undecidable for the groups $\mathrm{UT}_n(\mathbb{Z})$ of upper unitriangular integer matrices, $\mathrm{GL}_n(\mathbb{Z})$ and $\mathrm{SL}_n(\mathbb{Z})$ (Corollary 3).

The bound $322$ is that of the copy read; the abstract of the published article states the theorem for derived subgroups of rank at least $316$, which implies the statement above.

## Depends on

- [Knapsack problem for a finitely generated group](knapsack-problem-for-a-group.md)
- [Group](../../../group-basics/group.md)
- [Commutator subgroup of a group](../../../commutators-and-engel-conditions/commutator-subgroup.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Every recursively enumerable set $W$ is the set of integers $x$ for which a fixed system of quadratic Diophantine equations with parameters has a solution (by the negative solution of Hilbert's tenth problem). In a class-2 nilpotent group, products of powers of elements multiply out to polynomials of degree at most two in the exponents, with the commutator subgroup carrying the quadratic terms; when $[G, G]$ has rank greater than 322 there is room to encode such a system, giving a knapsack instance with 334 elements that is solvable exactly when $x \in W$ (Lemma 1). For the matrix groups, the free nilpotent group of class 2 and rank 26 embeds in $\mathrm{UT}_{53}(\mathbb{Z})$ by an explicit embedding of the free class-2 group of rank $k$ into $\mathrm{UT}_{2k+1}(\mathbb{Z})$, and $\mathrm{UT}_n(\mathbb{Z})$ lies in $\mathrm{SL}_n(\mathbb{Z}) \le \mathrm{GL}_n(\mathbb{Z})$; undecidability of the knapsack problem passes from a finitely generated subgroup to the group. Free nilpotent groups of class 2 and rank $n$ have derived subgroup of rank $\binom{n}{2}$, which exceeds 322 for $n \ge 26$.

## Sources

- A. Mishchenko and A. Treier, "Knapsack problem for nilpotent groups", Groups Complexity Cryptology 9 (2017), no. 1, https://doi.org/10.1515/gcc-2017-0006; read in arXiv:1606.08584v1 (Theorem 1, Corollaries 1 and 3, and Lemma 1, numbered separately by type, of arXiv:1606.08584v1).
