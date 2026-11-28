# Temporal free description logics with non-rigid designators are undecidable

Satisfiability of the temporal description logic LTL over ALCO with the universal role becomes undecidable when individual names may denote different objects at different instants, and it is undecidable with definite descriptions even when individual names are rigid.

**Theorem (Artale and Mazzullo).** Let $N_C$, $N_R$, $N_I$ be disjoint countably infinite sets of concept, role and individual names. Terms are $\tau ::= a \mid \iota C$ with $a \in N_I$, and $\mathrm{LTL}_{\mathcal{ALCO}_u^\iota}$ concepts and formulas are

$$
C ::= A \mid \{\tau\} \mid \neg C \mid C \sqcap C \mid \exists r.C \mid \exists u.C \mid C\,\mathcal U\,C, \qquad \varphi ::= C \sqsubseteq D \mid C(\tau) \mid r(\tau_1, \tau_2) \mid \neg\varphi \mid \varphi \wedge \varphi \mid \varphi\,\mathcal U\,\varphi,
$$

with $A \in N_C$, $r \in N_R$ and the universal role $u$; $\mathrm{LTL}_{\mathcal{ALCO}_u}$ is the fragment without definite descriptions $\iota C$. A *partial trace* $\mathcal M = (\mathbb N, \Delta, \mathcal I)$ has one nonempty domain $\Delta$ and, for each instant $t \in \mathbb N$, an interpretation $\mathcal I_t$ of concept and role names (with $u^{\mathcal I_t} = \Delta \times \Delta$) and a partial map from $N_I$ to $\Delta$; it is *total* if every $\mathcal I_t$ is defined on all individual names. The value of $\iota C$ at $t$ is the unique element of $C^{\mathcal I_t}$ if $C^{\mathcal I_t}$ is a singleton, and undefined otherwise; $\{\tau\}^{\mathcal I_t}$ is $\{\tau^{\mathcal I_t}\}$ if $\tau$ denotes at $t$, and $\emptyset$ otherwise; $(C\,\mathcal U\,D)^{\mathcal I_t}$ is the set of $d$ with $d \in D^{\mathcal I_{t'}}$ for some $t' > t$ and $d \in C^{\mathcal I_v}$ for all $t < v < t'$; and $\mathcal M, t \models C(\tau)$ requires $\tau$ to denote at $t$. A trace satisfies the *rigid designator assumption* (RDA) if every individual name that denotes at two instants denotes the same element at both. A formula is satisfiable if it holds at instant $0$ of some trace. Then:

1. satisfiability of $\mathrm{LTL}_{\mathcal{ALCO}_u}$ formulas without the RDA is undecidable;
2. satisfiability of $\mathrm{LTL}_{\mathcal{ALCO}_u^\iota}$ formulas with the RDA is undecidable;

already for satisfiability in total traces (Theorem 2 of the extended abstract; Theorem 3, Theorem 4 and Corollary 1 of the extended version).

By contrast, satisfiability without the RDA in the epistemic free description logic over S5 frames is NEXPTIME-complete, and the temporal logic is decidable without definite descriptions under the RDA. The modal counterpart over Kripke frames, with its own undecidability result for global ontologies, is on [Modal free description logics with non-rigid designators](modal-free-description-logics-with-non-rigid.md). The extended version states the same undecidability for finite traces.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)
- [Formulas of linear temporal logic](../../temporal-logic/linear-temporal-logic/formula.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proofs reduce the halting problem for two-counter Minsky machines started with both counters at $0$, adapting the reduction of Degtyarev, Fisher and Lisitsa for monodic first-order temporal logic with equality. There, equality encodes adding or subtracting one unit from a counter at the next step of a computation; here the same effect comes from the interplay between non-rigid, possibly non-denoting, nominals and the universal role. Without the RDA, rigidity of a name $a$ can still be forced by the inclusion $\lozenge^+\{a\} \sqsubseteq \square^+\{a\}$, so dropping the RDA is the more general setting.

## Sources

- A. Artale and A. Mazzullo, "Non-Rigid Designators in Epistemic and Temporal Free Description Logics (Extended Abstract)", in *Proceedings of the 36th International Workshop on Description Logics (DL 2023)*, CEUR Workshop Proceedings 3515, 2023, abstract 4; read in the open-access copy at <https://ceur-ws.org/Vol-3515/abstract-4.pdf>: Section 2 (syntax, partial and total traces, the RDA, Theorems 1 and 2).
- A. Artale and A. Mazzullo, "Non-Rigid Designators in Epistemic and Temporal Free Description Logics (Extended Version)", arXiv:2308.08640v1, <https://arxiv.org/abs/2308.08640v1>: Theorem 3 (with the Minsky machine reduction), Theorem 4 and Corollary 1, cited only beside the refereed extended abstract.
