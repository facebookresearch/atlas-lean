# Verification of relational multiagent systems with a successor data type is undecidable

Relational multiagent systems let agents keep relational databases and exchange messages carrying data. Once one data type has a successor relation, even reachability of a propositional property is undecidable, already for state-bounded systems with a single agent over unary relations.

**Setting (Calvanese, Delzanno and Montali).** A *data type* $\langle \Delta, \Gamma \rangle$ is an infinite domain $\Delta$ with a set $\Gamma$ of relations on it, for example $\langle \mathbb{Z}, \{<, =, \mathit{succ}\} \rangle$; a *facet* restricts a data type by a monadic formula, and a *base facet* is a whole data type. A *relational multiagent system* (RMAS) consists of finitely many agent specifications, each given by a database schema typed by facets, integrity constraints, an initial database instance, *communicative rules* $Q(t, \vec{x}) \mapsto M(\vec{x}) \to t$ that let an agent send a message $M$ with payload $\vec{x}$ to an agent $t$ when the domain-independent first-order query $Q$ holds over its database, and update rules that change the database when messages are sent or received, possibly calling external services, each of which returns an arbitrary data object of its output facet (possibly a fresh one); integrity constraints are domain-independent first-order formulas as well. An RMAS induces a relational transition system whose states are the databases of the currently active agents. It is *shallow-typed* if all its facets are base facets, and *state-bounded* if some bound limits the number of data objects stored in each agent database in every reachable state. The *verification problem* asks whether a property of the first-order $\mu$-calculus $\mu\mathcal{L}^{@}_p$ holds in the transition system of a given RMAS; a *propositional reachability property* asks whether a state satisfying a proposition is reachable.

**Theorem (Calvanese, Delzanno and Montali).** Verification of a propositional reachability property over state-bounded, shallow-typed RMASs that use a single data type equipped with the successor relation is undecidable, even when the RMAS contains a single agent that uses unary relations only.

In contrast, the same paper shows that verification of all closed $\mu\mathcal{L}^{@}_p$ properties is decidable for state-bounded densely-ordered RMASs, whose data types carry only equality and, possibly, a total dense order (Theorem 5.3), through a finite-state abstraction.

## Depends on

- [Relational schema](../../../databases/dependencies-and-the-chase/relational-schema.md)
- [Database instance](../../../databases/dependencies-and-the-chase/instance.md)
- [Relational calculus and domain independence](../../../databases/relational-calculus/relational-calculus-and-domain-independence.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof encodes a two-counter Minsky machine started with both counters at $0$. A single institutional agent, typed over the integers with successor, stores the current and previous values of the two counters, the program counter, the pending operation and the target counter in unary relations, so each relation holds at most one value and the system is state-bounded. The agent repeatedly sends itself a message triggering the next instruction; on an increment or decrement its update rules move the current value of the target counter to the previous-value relation and store an integer returned by an external service, which need not be fresh (a decrement stores a value already seen), and integrity constraints keep only successor states in which the returned value is the successor (respectively predecessor) of the previous one; conditional decrements test the counter against the constant $0$, and the last instruction sets $\mathit{Halted}$. A state with the proposition $\mathit{Halted}$ is reachable exactly when the machine halts.

## Sources

- Diego Calvanese, Giorgio Delzanno and Marco Montali, *Verification of Relational Multiagent Systems with Data Types*, Proceedings of the Twenty-Ninth AAAI Conference on Artificial Intelligence (AAAI 2015), 29(1), 2015, https://doi.org/10.1609/aaai.v29i1.9438; Theorem 5.2, read in the open-access copy at https://ojs.aaai.org/index.php/AAAI/article/view/9438, with the model and the proof read in the extended version arXiv:1411.4516v1.
