# Conflict-driven clause learning as a proof system

A CDCL refutation of a CNF formula is a sequence of trails, each built by decisions and unit propagation until a conflict, together with one clause learned from each trail by resolving antecedent clauses backwards; the run ends when the empty clause is learned.

Let $\phi$ be a CNF formula in $n$ variables. A **trail** is a sequence of literals

$$
\mathcal{T} = (p_{(0,1)}, \dots, p_{(0,g_0)}; \mathbf{d_1}, p_{(1,1)}, \dots, p_{(1,g_1)}; \dots; \mathbf{d_r}, p_{(r,1)}, \dots, p_{(r,g_r)}),
$$

possibly ending in $\bot$, where the $d_i$ are **decision literals** on pairwise distinct variables and each **propagated literal** $p_{(i,j)}$ has an **antecedent clause** $C \in \phi$ whose restriction by the preceding part of the trail is the unit clause $(p_{(i,j)})$ (for $\bot$, the restriction is empty, a **conflict**). A trail is **natural** if no available unit propagation is skipped and a conflict is taken as soon as one is available. From a trail ending in $\bot$, the **learnable clauses** are the clauses of the sequence obtained by starting from the antecedent of $\bot$ and resolving, in reverse propagation order, with the antecedent of each propagated literal whose complement occurs in the current clause (trivial resolution); in the propositional case no reduction steps occur.

A **CDCL proof** of a clause $C$ from $\phi$ is a triple of sequences of trails $\mathcal{T}_1, \dots, \mathcal{T}_m$, learned clauses $C_1, \dots, C_m$ with $C_i$ learnable from $\mathcal{T}_i$ and $C_m = C$, and their resolution derivations, where $\mathcal{T}_i$ is a trail for $\phi \cup \{C_1, \dots, C_{i-1}\}$, $\mathcal{T}_1$ is natural, and each $\mathcal{T}_i$ with $i \ge 2$ agrees with $\mathcal{T}_{i-1}$ up to some point and continues naturally from there (**backtracking**; backtracking to the empty trail is a **restart**). It is a **refutation** when $C = \bot$. Its size is $\sum_{j} |\mathcal{T}_j| = O(mn)$. Clauses are never deleted in this model.

## Expansion

The model is the propositional case (all variables existential, so the reduction rule is vacuous) of the QCDCL proof systems of Beyersdorff and Böhm, and it formalizes the informal description of CDCL in Nordström's survey: DPLL search with unit propagation, conflict analysis that learns a clause derived by trivial resolution over the propagated literals in reverse order (for example the 1UIP scheme), backjumping, and restarts. Every learned clause comes with a resolution derivation, so a CDCL refutation yields a resolution refutation of comparable size; without learning, the search trees are exactly tree-like resolution refutations.

## Depends on

- [Resolution refutation](../../../propositional-logic/resolution-size-and-width/is-resolution-refutation.md)

## Proof depends on

None.

## Sources

- O. Beyersdorff, B. Böhm, "Understanding the relative strength of QBF CDCL solvers and QBF resolution", *Logical Methods in Computer Science* 19(2:2), 2023 (conference version ITCS 2021), doi:10.46298/lmcs-19(2:2)2023, arXiv:2109.04862v5 (Definitions 3.1-3.5, restricted to the propositional case as in Section 7).
- J. Nordström, "On the interplay between proof complexity and SAT solving", *ACM SIGLOG News* 2(3), 2015, doi:10.1145/2743014.2743018 (Section 3 and Section 3.1).
