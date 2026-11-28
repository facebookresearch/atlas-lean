# Run-boundedness of data-centric dynamic systems is undecidable

A data-centric dynamic system evolves a relational database through actions that may call external services returning arbitrary new values. Whether every run of such a system uses only boundedly many distinct values, the condition under which verification becomes decidable, cannot be decided, even with deterministic services.

**Setting (Bagheri Hariri, Calvanese, De Giacomo, Deutsch and Montali).** A *data-centric dynamic system* (DCDS) $\mathcal{S} = \langle \mathcal{D}, \mathcal{P} \rangle$ has a *data layer* $\mathcal{D} = \langle C, \mathcal{R}, E, I_0 \rangle$, consisting of a countably infinite set of values $C$, a finite relational schema $\mathcal{R}$, finitely many equality constraints $E$ (implications from domain-independent first-order queries to equalities, such as keys) and an initial instance $I_0$ satisfying them; and a *process layer* $\mathcal{P} = \langle F, A, \varrho \rangle$, consisting of a finite set $F$ of service functions, a finite set $A$ of parameterized actions whose effects are rules $q^+_i \wedge Q^-_i \rightsquigarrow E_i$, pairing a union of conjunctive queries $q^+_i$ with a first-order filter $Q^-_i$ over the current instance and producing facts $E_i$ that may contain service calls $f(\dots)$, the next instance being the union of the grounded effects, and a finite set $\varrho$ of condition-action rules that say which actions may be executed with which parameters. Services are *deterministic* if a call with the same arguments returns the same value at every point of a run. The concrete transition system of $\mathcal{S}$ has as states pairs $\langle I, \mathcal{M} \rangle$ of an instance $I$ over $C$ satisfying $E$ and a service-call map $\mathcal{M}$ recording the results of the calls made so far, labelled by the instance $I$; it starts from $\langle I_0, \emptyset \rangle$, with a transition for every applicable action instance and every choice of results for new service calls, calls already in $\mathcal{M}$ returning their recorded values (determinism), provided the resulting instance satisfies $E$. A run is *bounded by* $b$ if fewer than $b$ distinct values occur in the active domains of the instances of all its states together, and $\mathcal{S}$ is *run-bounded* if some $b$ bounds every run.

**Theorem (Bagheri Hariri, Calvanese, De Giacomo, Deutsch and Montali).** Checking run-boundedness of DCDSs with deterministic services is undecidable.

The same paper shows that, for DCDSs with deterministic services, verification is undecidable in general (already for propositional LTL safety properties), while verification of properties in the first-order $\mu$-calculus fragment $\mu\mathcal{L}_A$ is decidable for run-bounded systems, and gives weak acyclicity as a sufficient syntactic condition for run-boundedness.

## Depends on

- [Relational schema](../../../databases/dependencies-and-the-chase/relational-schema.md)
- [Database instance](../../../databases/dependencies-and-the-chase/instance.md)
- [Relational calculus and domain independence](../../../databases/relational-calculus/relational-calculus-and-domain-independence.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The reduction is from the halting problem of deterministic Turing machines. A configuration is stored in relations $\mathit{right}(x, y)$ (cell $y$ is the right neighbor of cell $x$), $\mathit{sym}(c, s)$, $\mathit{head}(c)$, the state, and a flag $\mathit{halted}$; tape cells are values. A single always-enabled action simulates one machine step, calling a service to obtain a fresh cell identifier whenever the head moves past the visited segment. Runs of the DCDS correspond one-to-one to runs of the machine, and the values a run uses grow with the visited tape segment, so the system is run-bounded exactly when the machine's run stays within a bounded segment of the tape (it is tape-bounded). The source's proof of Theorem 4.6 concludes "TM halts if and only if S is run-bounded"; a machine that runs forever inside a bounded segment shows that this needs one more step, which the same paper supplies in its proof of Theorem 5.5: tape-boundedness is undecidable, since from a deterministic machine $T$ one builds a machine $T'$ that simulates $T$ while recording its configurations and, on seeing a configuration repeat, keeps extending the tape, so that $T'$ is tape-bounded exactly when $T$ halts. A good expansion adds a page for the undecidability of tape-boundedness.

## Sources

- Babak Bagheri Hariri, Diego Calvanese, Giuseppe De Giacomo, Alin Deutsch and Marco Montali, "Verification of relational data-centric dynamic systems with external services", Proceedings of the 32nd ACM SIGMOD-SIGACT-SIGART Symposium on Principles of Database Systems (PODS 2013), pp. 163–174, 2013, <https://doi.org/10.1145/2463664.2465221>; read in arXiv:1203.0024v1, <https://arxiv.org/abs/1203.0024v1>: the definitions of Sections 2 ("Data-Centric Dynamic Systems") and 4 ("Deterministic Services"), Theorem 4.6 (undecidability of run-boundedness), Theorem 4.1 (undecidability of verification, with the Turing machine construction in its proof), Theorem 4.2 (decidability for run-bounded systems) and Theorem 4.7 (weak acyclicity), in the numbering of that version.
