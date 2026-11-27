# Feasible interpolation for QBF resolution calculi

The strongest CDCL-based calculus $\mathsf{LQU^+\text{-}Res}$ and the strongest expansion-based calculus IRM-calc have monotone feasible interpolation, which yields exponential lower bounds for QBFs whose unique interpolant is the clique function.

Consider a false QBF $\mathcal{F} = \exists \vec{p}\, \mathcal{Q} \vec{q}\, \mathcal{Q} \vec{r} .\, [A(\vec{p}, \vec{q}) \land B(\vec{p}, \vec{r})]$ with $A, B$ CNFs, pairwise disjoint variable sets and arbitrary quantification of $\vec{q}$ and $\vec{r}$. An **interpolation circuit** for $\mathcal{F}$ is a Boolean circuit $G$ such that for every assignment $\vec{a}$ to $\vec{p}$, $G(\vec{a}) = 0$ implies that $\mathcal{Q} \vec{q} .\, A(\vec{a}, \vec{q})$ is false and $G(\vec{a}) = 1$ implies that $\mathcal{Q} \vec{r} .\, B(\vec{a}, \vec{r})$ is false. A QBF proof system has **feasible interpolation** if from any proof $\pi$ of such an $\mathcal{F}$ one can effectively extract an interpolation circuit of size polynomial in $|\pi|$, and **monotone feasible interpolation** if moreover the extracted circuit is monotone whenever $\vec{p}$ occurs only positively in $A$.

**Theorem.**

1. $\mathsf{LQU^+\text{-}Res}$ and IRM-calc have feasible interpolation, and both have monotone feasible interpolation.
2. Let $\Phi_n = \exists \vec{p}\, \exists \vec{q}\, \forall \vec{r}_1\, \exists \vec{r}_2 .\, A_n(\vec{p}, \vec{q}) \land B_n(\vec{p}, \vec{r}_1, \vec{r}_2)$, where $\vec{p}$ encodes an $n$-vertex graph, $A_n$ states with positive occurrences of $\vec{p}$ that $\vec{q}$ is a clique of size $n/2$, and $B_n$ is a CNF encoding of a polynomial-size circuit checking that the vertex set chosen by $\vec{r}_1$ is not a clique. Then $\Phi_n$ requires exponential-size proofs in IRM-calc and in $\mathsf{LQU^+\text{-}Res}$.

Since IRM-calc and $\mathsf{LQU^+\text{-}Res}$ simulate the other resolution-based QBF calculi considered (Q-resolution, QU-resolution, long-distance Q-resolution, universal expansion resolution, IR-calc), all of them have monotone feasible interpolation.

## Expansion

From a proof $\pi$ build a circuit $C_\pi$ on the DAG of $\pi$: leaves from $A$ get constant $0$, leaves from $B$ get constant $1$, and internal gates depend on the pivot. For each assignment $\vec{a}$, construct a proof-like structure whose clauses are subclauses of those of $\pi$, restrict it by $\vec{a}$ and prune it into a valid proof; by induction, if a gate evaluates to $0$ the corresponding clause is derivable from $A(\vec{a}, \vec{q})$ alone, and if $1$ from $B(\vec{a}, \vec{r})$ alone, so soundness gives the interpolation property at the root. For purely existential formulas this is Pudlák's interpolant for resolution. The clique formula has $\mathrm{Clique}(n, n/2)$ as unique interpolant, and monotone circuits for it are exponential (Alon-Boppana), giving item 2. Unlike strategy extraction, the method also applies to expansion-based calculi.

## Depends on

- [Q-resolution and its long-distance and universal variants](q-resolution-calculi.md)
- [Expansion-based QBF calculi: universal expansion resolution and IR-calc](expansion-based-qbf-calculi.md)

## Proof depends on

- [Interpolants from resolution refutations](../../../propositional-logic/proof-certificates/interpolants-from-resolution-refutations.md)
- [Alon-Boppana monotone clique lower bound](../../../../TheoryOfComputation/circuit-complexity/monotone-circuit-lower-bound-for-clique/alon-boppana-monotone-clique.md)

## Sources

- O. Beyersdorff, L. Chew, M. Mahajan, A. Shukla, "Feasible interpolation for QBF resolution calculi", *Logical Methods in Computer Science* 13(2:7), 2017 (conference version ICALP 2015), doi:10.23638/LMCS-13(2:7)2017, arXiv:1611.01328v3 (Section 3.1 with the interpolation definitions, Theorems 3.3 and 3.4, the monotone interpolation theorem of Section 3.4, Theorem 4.2 in Section 4).
