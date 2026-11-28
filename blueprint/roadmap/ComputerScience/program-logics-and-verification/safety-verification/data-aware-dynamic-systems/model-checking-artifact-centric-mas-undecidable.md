# Model checking artifact-centric multi-agent systems is undecidable

Artifact-centric multi-agent systems describe agents and an environment whose local states are relational databases over an infinite domain, evolving by parameterized actions. Model checking them against first-order temporal-epistemic specifications is undecidable.

**Setting (Belardinelli, Lomuscio and Patrizi).** Fix an interpretation domain $U$, possibly infinite. An *agent* is a tuple $\langle \mathcal{D}, L, \mathit{Act}, \mathit{Pr} \rangle$ of a local database schema $\mathcal{D}$, a set $L$ of local states that are database instances of $\mathcal{D}$ over $U$, a finite set $\mathit{Act}$ of action types $\alpha(\vec{p})$ with abstract parameters, and a local protocol $\mathit{Pr}$ assigning to each local state a set of ground actions $\alpha(\vec{u})$ with $\vec{u}$ from $U$. An *artifact-centric multi-agent system* (AC-MAS) composes an environment agent, whose state holds all artifacts, with agents $A_1, \dots, A_n$ synchronously: global states are tuples of local states, an initial global state is given, and a transition function maps a global state and a joint ground action, allowed by all protocols, to successor states. *FO-CTLK* formulas over a database schema are generated from first-order formulas by negation, implication, first-order quantification $\forall x$, the temporal operators $AX$, $A\,U$, $E\,U$, the knowledge operators $K_i$ and common knowledge $C$; knowledge is interpreted by indistinguishability of agents' local states. *Model checking* an AC-MAS against an FO-CTLK formula asks whether the formula holds at the initial state under some assignment to its free variables.

**Theorem (Belardinelli, Lomuscio and Patrizi).** The model checking problem for artifact-centric multi-agent systems with respect to FO-CTLK is undecidable.

An AC-MAS over an infinite domain is an infinite object, and the source does not fix how one is given to an algorithm. The statement proved is about the systems its reduction builds: from a Turing machine $T$ and an input $I$ one effectively constructs an AC-MAS $P_{T,I}$, and with an FO-CTLK formula $\varphi$ expressing termination, $P_{T,I}$ satisfies $\varphi$ exactly when $T$ halts on $I$ (proof sketch of Theorem 2.11, following Theorem 4.10 of Deutsch, Sui and Vianu). So no algorithm decides model checking for the systems so constructed, given by $(T, I)$.

When $U$ is finite the system is finite-state and the problem is decidable; the same paper identifies bounded and uniform systems, and a syntactic class of artifact-centric programs, for which model checking reduces to the finite-state case.

## Depends on

- [CTL formulas](../../../../Logic/temporal-logic/computation-tree-logic/formula.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Every Turing machine $T$ with an initial tape content $I$ can be simulated by an AC-MAS $\mathcal{P}_{T,I}$, whose environment database stores the tape as relations over the infinite domain and whose actions perform machine steps. Termination of $T$ on $I$ is expressed by an FO-CTLK formula $\varphi$, so termination reduces to deciding whether $\mathcal{P}_{T,I}$ satisfies $\varphi$; the construction follows an earlier Turing machine simulation from the verification of data-driven systems.

## Sources

- Francesco Belardinelli, Alessio Lomuscio and Fabio Patrizi, "Verification of Agent-Based Artifact Systems", Journal of Artificial Intelligence Research 51, pp. 333–376, 2014, <https://doi.org/10.1613/jair.4424>; Definitions 2.6 (agents), 2.7 (artifact-centric multi-agent systems), 2.8 and 2.9 (FO-CTLK and its satisfaction) and 2.10 (model checking), and Theorem 2.11 with its proof sketch, in Sections 2.2 and 2.3 of arXiv:1301.2678v2, read at <https://arxiv.org/abs/1301.2678v2>.
