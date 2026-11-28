# QCDCL proof systems

QCDCL refutations of a false QBF are sequences of trails built by decisions and unit propagation with universal reduction, each ending in a conflict, together with clauses learned by long-distance Q-resolution; policies fix the decision order and whether propagation may use reduction.

Let $\Phi = \mathcal{Q} \cdot \phi$ be a QCNF in $n$ variables. A **trail** for $\Phi$ is a sequence of decision literals (existential or universal, on pairwise distinct variables) and propagated literals (existential, or $\bot$ as the last element), grouped into decision levels. A **decision policy** is one of

- $\mathsf{LEV\text{-}ORD}$: decisions follow the quantifier order (always a remaining variable of lowest level);
- $\mathsf{EXI\text{-}ANY\text{-}NO\text{-}RED}$: a literal $d_k$ may be decided if it is existential, or if it is universal and the levels of all decisions so far, existential ones included and $d_k$ itself last, are nondecreasing: $\mathrm{lv}(d_1) \le \dots \le \mathrm{lv}(d_k)$;
- $\mathsf{UNI\text{-}ANY}$: an existential variable may be decided only after all universal variables of smaller level are assigned;
- $\mathsf{ANY}$: any remaining literal may be decided.

These are the names of the cited edition; arXiv v1 and the ITCS 2021 version call the same policies $\mathsf{LEV\text{-}ORD}$, $\mathsf{ASS\text{-}ORD}$, $\mathsf{ASS\text{-}R\text{-}ORD}$ and $\mathsf{ANY\text{-}ORD}$.

A **unit-propagation policy** is $\mathsf{RED}$, where a propagated literal $p$ needs an antecedent $C \in \phi$ with $\mathrm{red}(C|_{\mathcal{T}}) = (p)$ (reduction allowed), or $\mathsf{NO\text{-}RED}$, where it needs $C|_{\mathcal{T}} = (p)$; here $\mathrm{red}$ deletes the universal literals quantified after all existential literals of the clause. From a trail ending in $\bot$ the **learnable clauses** are obtained by resolving the reduced antecedent of $\bot$ backwards with the reduced antecedents of the propagated literals whose complements occur, applying reduction after each step. A $\mathsf{QCDCL}^P_R$ **proof** of $C$ is a triple of sequences of trails $\mathcal{T}_1, \dots, \mathcal{T}_m$ following the policies, learned clauses $C_1, \dots, C_m = C$ with $C_i$ learnable from $\mathcal{T}_i$ over $\phi \cup \{C_1, \dots, C_{i-1}\}$, and their derivations, where $\mathcal{T}_1$ is natural and each later trail backtracks into its predecessor and then continues naturally (backtracking to the empty trail is a restart). It is a refutation if $C = \bot$, and its size is $\sum_j |\mathcal{T}_j|$.

## Expansion

$\mathsf{QCDCL}^{\mathsf{LEV\text{-}ORD}}_{\mathsf{RED}}$ is classical QCDCL as implemented in solvers. The order condition of $\mathsf{EXI\text{-}ANY\text{-}NO\text{-}RED}$ ranges over existential decisions too. Under $\mathsf{ANY}$ and $\mathsf{NO\text{-}RED}$, for $\forall u \exists x .\, (u \lor x)(u \lor \overline{x})(\overline{u} \lor x)(\overline{u} \lor \overline{x})$ the trail with decisions $x$ then $u$ ends in a conflict from which no asserting clause can be learned (the source's Remark 3.11), while under $\mathsf{EXI\text{-}ANY\text{-}NO\text{-}RED}$ and $\mathsf{NO\text{-}RED}$ every trail ending in a conflict whose learnable clauses do not include the empty clause has an asserting learnable clause (Lemma 3.14). All these systems are sound and complete. The derivations of learned clauses are long-distance Q-resolution derivations, and with $\mathsf{NO\text{-}RED}$ no tautologies arise, so they are Q-resolution derivations; universal tautologies can only come from reductions during propagation. Cube learning for true formulas is omitted, since only refutations are compared with Q-resolution.

## Depends on

- [Q-resolution and its long-distance and universal variants](q-resolution-calculi.md)
- [Cook–Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- O. Beyersdorff, B. Böhm, "Understanding the relative strength of QBF CDCL solvers and QBF resolution", *Logical Methods in Computer Science* 19(2:2), 2023 (conference version ITCS 2021), doi:10.46298/lmcs-19(2:2)2023, arXiv:2109.04862v5 (Section 2.4 and Definitions 3.1-3.5, with the policy names of this edition; Theorem 3.9 on simulation by long-distance Q-resolution; Remark 3.11 and Lemma 3.14 on asserting clauses).
