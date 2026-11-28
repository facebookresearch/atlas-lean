# Run-boundedness of data-centric dynamic systems is undecidable

A data-centric dynamic system evolves a relational database through actions that may call external services returning arbitrary new values. Whether every run of such a system uses only boundedly many distinct values, the condition under which verification becomes decidable, cannot be decided, even with deterministic services.

**Setting (Bagheri Hariri, Calvanese, De Giacomo, Deutsch and Montali).** A *data-centric dynamic system* (DCDS) $\mathcal{S} = \langle \mathcal{D}, \mathcal{P} \rangle$ has a *data layer* $\mathcal{D} = \langle C, \mathcal{R}, E, I_0 \rangle$, consisting of a countably infinite set of values $C$, a finite relational schema $\mathcal{R}$, finitely many equality constraints $E$ (implications from domain-independent first-order queries to equalities, such as keys) and an initial instance $I_0$ satisfying them; and a *process layer* $\mathcal{P} = \langle F, A, \varrho \rangle$, consisting of a finite set $F$ of service functions, a finite set $A$ of parameterized actions whose effects are rules that query the current instance and build the next instance from query answers and service calls $f(\dots)$, and a finite set $\varrho$ of condition-action rules that say which actions may be executed with which parameters. Services are *deterministic* if a call with the same arguments returns the same value at every point of a run. The concrete transition system of $\mathcal{S}$ has database instances as states, starting from $I_0$, with a transition for every applicable action instance and every choice of service results compatible with determinism, provided the resulting instance satisfies $E$. A run is *bounded by* $b$ if fewer than $b$ distinct values occur in the active domains of all its states together, and $\mathcal{S}$ is *run-bounded* if some $b$ bounds every run.

**Theorem (Bagheri Hariri, Calvanese, De Giacomo, Deutsch and Montali).** Checking run-boundedness of DCDSs with deterministic services is undecidable.

The same paper shows that, for DCDSs with deterministic services, verification is undecidable in general (already for propositional LTL safety properties), while verification of properties in the first-order $\mu$-calculus fragment $\mu\mathcal{L}_A$ is decidable for run-bounded systems, and gives weak acyclicity as a sufficient syntactic condition for run-boundedness.

## Depends on

- [Relational schema](../../../databases/dependencies-and-the-chase/relational-schema.md)
- [Database instance](../../../databases/dependencies-and-the-chase/instance.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The reduction is from the halting problem of deterministic Turing machines. A configuration is stored in relations $\mathit{right}(x, y)$ (cell $y$ is the right neighbor of cell $x$), $\mathit{sym}(c, s)$, $\mathit{head}(c)$, the state, and a flag $\mathit{halted}$; tape cells are values. A single always-enabled action simulates one machine step, calling a service to obtain a fresh cell identifier whenever the head moves past the visited segment. Runs of the DCDS correspond one-to-one to runs of the machine, so the system is run-bounded exactly when the machine halts.

## Sources

- Babak Bagheri Hariri, Diego Calvanese, Giuseppe De Giacomo, Alin Deutsch and Marco Montali, "Verification of relational data-centric dynamic systems with external services", Proceedings of the 32nd ACM SIGMOD-SIGACT-SIGART Symposium on Principles of Database Systems (PODS 2013), pp. 163–174, 2013, <https://doi.org/10.1145/2463664.2465221>; read in arXiv:1203.0024v1, <https://arxiv.org/abs/1203.0024v1>: the definitions of Sections 2 ("Data-Centric Dynamic Systems") and 4 ("Deterministic Services"), Theorem 4.6 (undecidability of run-boundedness), Theorem 4.1 (undecidability of verification, with the Turing machine construction in its proof), Theorem 4.2 (decidability for run-bounded systems) and Theorem 4.7 (weak acyclicity), in the numbering of that version.
