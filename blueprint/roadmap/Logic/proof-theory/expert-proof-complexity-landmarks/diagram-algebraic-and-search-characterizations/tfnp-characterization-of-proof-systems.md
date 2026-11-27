# Characterizing a proof system by a black-box TFNP problem

A black-box TFNP problem characterizes a proof system when the false-clause search problems of CNF formulas that reduce to it by shallow decision trees are exactly those of the formulas with polylogarithmic proof complexity, measured as degree plus logarithm of size.

**Black-box TFNP.** A total search problem is a sequence of relations $R_n \subseteq \{0,1\}^n \times O_n$ such that for each $x \in \{0,1\}^n$ some $i \in O_n$ has $(x, i) \in R_n$. It is in $\mathrm{TFNP}^{dt}$ if for each $i \in O$ there is a decision tree $T_i^o$ of depth $\mathrm{polylog}(n)$ with $T_i^o(x) = 1$ iff $(x, i) \in R_n$. For an unsatisfiable CNF formula $F = C_1 \wedge \dots \wedge C_m$, the **false-clause search problem** $S_F$ asks, given an assignment, for an index $i$ of a clause $C_i$ it falsifies.

**Decision-tree reductions.** A decision-tree reduction from $Q \subseteq \{0,1\}^s \times O'$ to $R \subseteq \{0,1\}^n \times O$ consists of decision trees $T_i : \{0,1\}^s \to \{0,1\}$ for $i \in [n]$ and $T_j^o : \{0,1\}^s \to O'$ for $j \in O$ such that for every $x \in \{0,1\}^s$,

$$
(T_1(x), \dots, T_n(x), j) \in R \Rightarrow (x, T_j^o(x)) \in Q .
$$

If $d$ is the maximum depth of the trees and $n$ the size, the complexity of the reduction is $\log n + d$, and $R^{dt}(Q)$ is the least complexity of a reduction from $Q$ to $R$. The class $R^{dt}$ is the set of $Q \in \mathrm{TFNP}^{dt}$ with $R^{dt}(Q) = \mathrm{polylog}(n)$.

**Proof complexity measure and characterization.** For a proof system $P$ with an associated degree measure (polynomial degree for Nullstellensatz, Polynomial Calculus and Sherali-Adams, clause width for resolution) and an unsatisfiable CNF formula $F$,

$$
P(F) := \min\{\deg(\Pi) + \log \mathrm{size}(\Pi) : \Pi \text{ is a } P\text{-proof of } F\} .
$$

A problem $R \in \mathrm{TFNP}^{dt}$ **characterizes** $P$ if $R^{dt} = \{S_F : P(F) = \mathrm{polylog}(n)\}$. Every $R \in \mathrm{TFNP}^{dt}$ is equivalent to $S_F$ for an unsatisfiable CNF $F$ on $|O|$ variables, namely the conjunction over $i \in O$ of the CNFs $\neg T_i^o$ expressing that each verifier rejects.

## Expansion

Since every problem in $\mathrm{TFNP}^{dt}$ is equivalent to a false-clause search problem, black-box TFNP is the study of the problems $S_F$, and a TFNP subclass defined by a complete problem corresponds to a proof system by the definition above. Instances recalled in the source: $\mathrm{FP}^{dt}$ is tree-like resolution, $\mathrm{PLS}^{dt}$ is resolution, $\mathrm{PPA}^{dt}$ is $\mathbb{F}_2$-Nullstellensatz, $\mathrm{PPA}_q^{dt}$ is $\mathbb{F}_q$-Nullstellensatz for prime $q$, $\mathrm{PPADS}^{dt}$ is unary Nullstellensatz, $\mathrm{PPAD}^{dt}$ is unary Sherali-Adams, and $\mathrm{SOPL}^{dt}$ and $\mathrm{EOPL}^{dt}$ are the reversible-resolution systems RevRes and RevResT; many of them hold in the stronger form $P(F) = \Theta(R^{dt}(S_F))$ for the canonical complete problem $R$. The measure $\deg + \log \mathrm{size}$ is the parameter that query-to-communication lifting theorems transfer to monotone circuit models.

## Depends on

- [Cook-Reckhow propositional proof systems](../../../propositional-logic/propositional-proof-complexity/cookreckhow-propositional-proof-systems.md)

## Proof depends on

None.

## Sources

- Sam Buss, Noah Fleming, Russell Impagliazzo, "TFNP Characterizations of Proof Systems and Monotone Circuits", *14th Innovations in Theoretical Computer Science Conference (ITCS 2023)*, LIPIcs, 2023, doi:10.4230/LIPIcs.ITCS.2023.30 (Section 2: definitions of $\mathrm{TFNP}^{dt}$, decision-tree reductions, the complexity measure $P(F)$ and characterization; Claim 1).
