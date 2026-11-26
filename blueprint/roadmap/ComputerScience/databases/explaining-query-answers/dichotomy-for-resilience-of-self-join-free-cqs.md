# Dichotomy for the resilience of self-join-free conjunctive queries

Let $q$ be a self-join-free Boolean conjunctive query with each atom marked endogenous or exogenous, and consider its dual
hypergraph, whose vertices are the atoms and whose hyperedges are, for each variable, the set of atoms containing it. An
endogenous atom $A$ *dominates* an endogenous atom $B$ when $\mathrm{var}(A) \subsetneq \mathrm{var}(B)$. A *triad* is a set of
three endogenous atoms $\{S_0, S_1, S_2\}$ such that for every pair $S_i, S_j$ there is a path from $S_i$ to $S_j$ that uses no
variable of the third atom.

**Theorem (Freire, Gatterbauer, Immerman and Meliou).** Let $q'$ be obtained from $q$ by marking all dominated atoms
exogenous. If $q'$ has a triad, then [$\mathrm{RES}(q)$](endogenous-facts-and-the-resilience-of-a-query.md) is NP-complete;
otherwise it is in polynomial time. Whether $q'$ has a triad can be checked in time polynomial in the size of $q$.

## Depends on

- [Endogenous facts and the resilience of a query](endogenous-facts-and-the-resilience-of-a-query.md)
- [The complexity class NP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)
- [NP-complete decision problems](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Edmonds-Karp computes a maximum flow and a minimum cut](../../graph-algorithms/spanning-trees-flows-matchings/edmonds-karp-algorithm/edmonds-karp-max-flow-min-cut.md)

## Sources

- C. Freire, W. Gatterbauer, N. Immerman and A. Meliou, "The complexity of resilience and responsibility for self-join-free conjunctive queries", *Proc. VLDB Endowment* 9(3) (2015) 180–191; extended version arXiv:1507.00674 <https://arxiv.org/abs/1507.00674>, Definitions 3.1, 3.6 and 3.7, Proposition 3.8, Theorem 3.24 and Corollary 3.25.
