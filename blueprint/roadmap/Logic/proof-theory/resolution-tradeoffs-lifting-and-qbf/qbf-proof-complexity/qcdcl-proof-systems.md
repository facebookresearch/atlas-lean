# QCDCL proof systems

QCDCL refutations of a false QBF are sequences of trails built by decisions and unit propagation with universal reduction, each ending in a conflict, together with clauses learned by long-distance Q-resolution; policies fix the decision order and whether propagation may use reduction.

Let $\Phi = \mathcal{Q} \cdot \phi$ be a QCNF in $n$ variables. A **trail** for $\Phi$ is a sequence of decision literals (existential or universal, on pairwise distinct variables) and propagated literals (existential, or $\bot$ as the last element), grouped into decision levels. A **decision policy** is one of

- $\mathsf{LEV\text{-}ORD}$: decisions follow the quantifier order (always a remaining variable of lowest level);
- $\mathsf{ASS\text{-}ORD}$: universal decisions must appear in nondecreasing level order, existential ones are unrestricted;
- $\mathsf{ASS\text{-}R\text{-}ORD}$: an existential variable may be decided only after all universal variables of smaller level are assigned;
- $\mathsf{ANY\text{-}ORD}$: any remaining literal may be decided.

A **unit-propagation policy** is $\mathsf{ALL\text{-}RED}$, where a propagated literal $p$ needs an antecedent $C \in \phi$ with $\mathrm{red}(C|_{\mathcal{T}}) = (p)$ (reduction allowed), or $\mathsf{NO\text{-}RED}$, where it needs $C|_{\mathcal{T}} = (p)$; here $\mathrm{red}$ deletes the universal literals quantified after all existential literals of the clause. From a trail ending in $\bot$ the **learnable clauses** are obtained by resolving the reduced antecedent of $\bot$ backwards with the reduced antecedents of the propagated literals whose complements occur, applying reduction after each step. A $\mathsf{QCDCL}^P_R$ **proof** of $C$ is a triple of sequences of trails $\mathcal{T}_1, \dots, \mathcal{T}_m$ following the policies, learned clauses $C_1, \dots, C_m = C$ with $C_i$ learnable from $\mathcal{T}_i$ over $\phi \cup \{C_1, \dots, C_{i-1}\}$, and their derivations, where $\mathcal{T}_1$ is natural and each later trail backtracks into its predecessor and then continues naturally (backtracking to the empty trail is a restart). It is a refutation if $C = \bot$, and its size is $\sum_j |\mathcal{T}_j|$.

## Expansion

$\mathsf{QCDCL}^{\mathsf{LEV\text{-}ORD}}_{\mathsf{ALL\text{-}RED}}$ is classical QCDCL as implemented in solvers. All these systems are sound and complete. The derivations of learned clauses are long-distance Q-resolution derivations, and with $\mathsf{NO\text{-}RED}$ no tautologies arise, so they are Q-resolution derivations; universal tautologies can only come from reductions during propagation. Cube learning for true formulas is omitted, since only refutations are compared with Q-resolution.

## Depends on

- [Q-resolution and its long-distance and universal variants](q-resolution-calculi.md)

## Proof depends on

None.

## Sources

- O. Beyersdorff, B. Böhm, "Understanding the relative strength of QBF CDCL solvers and QBF resolution", *Logical Methods in Computer Science* 19(2:2), 2023 (conference version ITCS 2021), doi:10.46298/lmcs-19(2:2)2023, arXiv:2109.04862v5 (Section 2.4 and Definitions 3.1-3.5, Theorem 3.9 on simulation by long-distance Q-resolution).
