# Model checking artifact-centric multi-agent systems is undecidable

Artifact-centric multi-agent systems describe agents and an environment whose local states are relational databases over an infinite domain, evolving by parameterized actions. Model checking them against first-order temporal-epistemic specifications is undecidable.

**Setting (Belardinelli, Lomuscio and Patrizi).** Fix a countable interpretation domain $U$, possibly infinite. An *agent* is a tuple $\langle \mathcal{D}, \mathit{Act}, \mathit{Pr} \rangle$ of a local database schema $\mathcal{D}$, a finite set $\mathit{Act}$ of action types $\alpha(\vec{p})$ with abstract parameters, and a local protocol function $\mathit{Pr}\colon \mathcal{D}(U) \to 2^{\mathit{Act}(U)}$ assigning to each database instance of $\mathcal{D}$ over $U$ (each local state) a set of ground actions $\alpha(\vec{u})$ with $\vec{u}$ from $U$ (instances are finite: each relation symbol is interpreted by a finite relation over $U$, Definition 2.2). An *artifact-centric multi-agent system* (AC-MAS) $\langle \mathit{Ag}, s_0, \tau \rangle$ composes an environment agent, whose state holds all artifacts, with agents $A_1, \dots, A_n$ synchronously: global states are tuples of local states, $s_0$ is the initial global state, and the transition function $\tau$ maps a global state and a joint ground action, allowed by all protocols, to successor states; as in the source, the transition relation is assumed serial (each agent has a skip action enabled at every local state, which changes nothing), so every state has a successor and runs are infinite (Section 2.2). *FO-CTLK* formulas over a database schema are generated from first-order formulas by negation, implication, first-order quantification $\forall x$ (as in the source, quantifiers in first-order and FO-CTLK formulas range over the active domain of the instance or state where the formula is evaluated, Definitions 2.4 and 2.9), the temporal operators $AX$, $A\,U$, $E\,U$, the knowledge operators $K_i$ and common knowledge $C$; knowledge is interpreted by indistinguishability of agents' local states over the set $S$ of global states reachable from $s_0$: $K_i\varphi$ holds at $s$ when $\varphi$ holds at every reachable state in which agent $i$ has the same local state as in $s$, and $C$ uses the transitive closure of the union of these relations (Definition 2.9). *Model checking* an AC-MAS against an FO-CTLK formula asks whether the formula holds at the initial state under some assignment to its free variables.

**Theorem (Belardinelli, Lomuscio and Patrizi).** The model checking problem for artifact-centric multi-agent systems with respect to FO-CTLK is undecidable.

For the decision problem, the source assumes that the protocol functions and the transition function are computable and finitely represented (for instance by Turing machines), so that every AC-MAS, infinite-state ones included, has a finite representation, and fixes the representation formalism. The proof effectively constructs, from a Turing machine $T$ and an input $I$, an AC-MAS $P_{T,I}$ with computable protocols and transition function such that, for an FO-CTLK formula $\varphi$ expressing termination, $P_{T,I}$ satisfies $\varphi$ exactly when $T$ halts on $I$ (proof sketch of Theorem 2.11, following Theorem 4.10 of Deutsch, Sui and Vianu).

When $U$ is finite the system is finite-state and the problem is decidable; the same paper identifies bounded and uniform systems, and a syntactic class of artifact-centric programs, for which model checking reduces to the finite-state case.

## Depends on

- [CTL formulas](../../../../Logic/temporal-logic/computation-tree-logic/formula.md)
- [Epistemic formulas](../../../../Logic/modal-logic/epistemic-logic/formula.md)
- [Relational schema](../../../databases/dependencies-and-the-chase/relational-schema.md)
- [Database instance](../../../databases/dependencies-and-the-chase/instance.md)
- [Active domain of a database instance](../../../databases/dependencies-and-the-chase/active-domain.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Every Turing machine $T$ with an initial tape content $I$ can be simulated by an AC-MAS $\mathcal{P}_{T,I}$, whose environment database stores the tape as relations over the infinite domain and whose actions perform machine steps. Termination of $T$ on $I$ is expressed by an FO-CTLK formula $\varphi$, so termination reduces to deciding whether $\mathcal{P}_{T,I}$ satisfies $\varphi$; the construction follows an earlier Turing machine simulation from the verification of data-driven systems.

## Sources

- Francesco Belardinelli, Alessio Lomuscio and Fabio Patrizi, "Verification of Agent-Based Artifact Systems", Journal of Artificial Intelligence Research 51, pp. 333–376, 2014, <https://doi.org/10.1613/jair.4424>; Definitions 2.6 (agents), 2.7 (artifact-centric multi-agent systems), 2.8 and 2.9 (FO-CTLK and its satisfaction) and 2.10 (model checking), Definition 2.2 (countable interpretation domains), the finite-representation assumption before Theorem 2.11, and Theorem 2.11 with its proof sketch, in Section 2 of the published version, read in its open-access copy at <https://jair.org/index.php/jair/article/download/10910/26015>; the earlier arXiv:1301.2678v2 states Theorem 2.11 in the same words.
