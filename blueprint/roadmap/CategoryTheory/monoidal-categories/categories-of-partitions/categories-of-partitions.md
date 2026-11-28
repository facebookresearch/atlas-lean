# Categories of partitions

A category of partitions is a set of partitions of finite point sets, drawn with upper and lower rows of points, that contains the identity and pair partitions and is closed under tensor product, involution and composition.

**Partitions.** For $k,\ell\in\mathbb N$, a *partition* with $k$ upper and $\ell$ lower points is a decomposition of $\{1,\dots,k+\ell\}$ into disjoint nonempty blocks; it is drawn as a string diagram with a row of $k$ upper points, a row of $\ell$ lower points, and strings joining points of the same block. Write $\mathcal P(k,\ell)$ for the set of these partitions and $\mathcal P$ for the set of all partitions; partitions with different numbers of upper and lower points are distinct even when their blocks agree.

**Operations.**

- The *tensor product* $p\otimes q\in\mathcal P(k_1+k_2,\ell_1+\ell_2)$ of $p\in\mathcal P(k_1,\ell_1)$ and $q\in\mathcal P(k_2,\ell_2)$ places the diagrams side by side.
- The *involution* $p^*\in\mathcal P(\ell,k)$ of $p\in\mathcal P(k,\ell)$ reflects the diagram in a horizontal axis.
- The *composition* $pq\in\mathcal P(k,m)$ of $p\in\mathcal P(\ell,m)$ and $q\in\mathcal P(k,\ell)$ places $q$ above $p$, identifies each lower point of $q$ with the corresponding upper point of $p$, and then removes these middle points, keeping the blocks connected through them (blocks lying entirely in the middle disappear).

**Definition.** A *category of partitions* is a subset $\mathcal C\subseteq\mathcal P$ that contains the identity partition in $\mathcal P(1,1)$, joining its two points, and the pair partition in $\mathcal P(0,2)$, joining its two lower points, and that is closed under tensor products, involutions and compositions. Write $\mathcal C(k,\ell)=\mathcal C\cap\mathcal P(k,\ell)$. Such a category is automatically closed under rotations and vertical reflections. It is *recursively enumerable* if some Turing machine enumerates its elements.

Examples are all partitions $\mathcal P$, the pair partitions (every block of size two), the non-crossing partitions, and the balanced partitions; intersections of categories of partitions are again categories of partitions. Categories of partitions arise in the representation theory of compact quantum groups (easy quantum groups) and are linked to diagram algebras such as the Temperley–Lieb algebra.

## Depends on

- [Partition of a set into nonempty pairwise disjoint blocks](../../../SetTheory/sets-functions-relations/set-partition.md)
- [Enumerating a predicate](../../../TheoryOfComputation/computability/enumerators/enumerates.md)

## Proof depends on

None.

## Sources

- N. Faroß and S. Volz, "Algorithmic problems in categories of partitions", in *Proceedings of the 2025 International Symposium on Symbolic and Algebraic Computation (ISSAC 2025)*, pp. 25–33, ACM, 2025, doi:[10.1145/3747199.3747543](https://doi.org/10.1145/3747199.3747543); read in arXiv:2502.05373v1 ([arXiv](https://arxiv.org/abs/2502.05373v1)): the definitions of partitions, tensor product, involution, composition and categories of partitions, with the examples, in the section "Preliminaries", and the definition of recursive enumerability in the section "Undecidability of category problems".
