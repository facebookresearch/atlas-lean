# Safety of parameterized programs with process identities is undecidable

Whether some instance of a parameterized program, made of arbitrarily many copies of one finite-state process that know their own indices and talk to their neighbors, reaches an unsafe state is undecidable, even though every single instance has finitely many states.

**Setting.** A *parameterized program* is a finite-state template executed by every process of a *crowd* of $N$ processes, for an arbitrary number $N$. With *process identities*, the template may refer to a process's own index $i \in \{1, \dots, N\}$ and to $N$ (for example in the test $i < N$), which lets processes be arranged as an array (or a ring, a tree, and so on) and send values to their left and right neighbors $i - 1$ and $i + 1$. The source motivates the setting by programs whose variables are booleans or range between $0$ and $N$, for which each fixed $N$ gives finitely many reachable configurations; it fixes neither the transition labels of a template, nor the communication mechanism between neighbors, nor the tests on $i$ and $N$, nor the initial configuration. The *parameterized reachability problem* asks, given the template and an unsafe local state, whether for some $N$ some execution of the crowd of $N$ processes reaches a configuration in which a process is in the unsafe state.

**Theorem.** The parameterized reachability problem for parameterized programs with process identities is undecidable.

The source gives this as a proof sketch in a survey and fixes no formal model of templates or of message passing. Its reduction simulates a Turing machine $M$ on an input $x$ with one process per tape cell, each process exchanging messages with its left and right neighbors; the unsafe configurations are those in which some process's control-state variable holds a final state of $M$, and some crowd reaches one exactly when $M$ accepts $x$: an accepting computation uses finitely many cells, say $N$, and the crowd of $N$ processes then reaches such a configuration.

Without identities the picture changes: for anonymous crowds communicating by rendezvous, broadcast or a global store, the same coverability question is decidable, with complexities ranging from NP-complete (global store without locking) through EXPSPACE-complete (global store with locking, by reduction to Petri net coverability) to non-primitive-recursive (broadcast), as surveyed by Esparza.

## Depends on

- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Given a Turing machine $M$ and an input $x$, the template simulates one tape cell: it stores whether the head is on the cell, the current tape symbol, and the control state of $M$ when the head is there, and it passes the head to its left or right neighbor by message passing. If $M$ accepts $x$, it uses only finitely many cells, say $N$, and the crowd of $N$ processes reaches a configuration in which some process holds an accepting control state of $M$; if $M$ does not accept $x$, no crowd ever does. Taking the accepting states as unsafe reduces acceptance of Turing machines to parameterized reachability.

A good expansion first fixes a model in which the sketch is a theorem, for example a linear array of copies of one finite automaton whose moves are internal moves or synchronous send-right/receive-from-left handshakes guarded by the tests $i = 1$ and $i = N$, with all processes starting in the initial state, and cites a source that states the result for that model.

## Sources

- Javier Esparza, "Keeping a Crowd Safe: On the Complexity of Parameterized Verification", invited talk in *31st International Symposium on Theoretical Aspects of Computer Science (STACS 2014)*, Leibniz International Proceedings in Informatics 25, Schloss Dagstuhl, 2014, pp. 1–10, doi:[10.4230/LIPIcs.STACS.2014.1](https://doi.org/10.4230/LIPIcs.STACS.2014.1); read in the [open-access copy](https://drops.dagstuhl.de/storage/00lipics/lipics-vol025-stacs2014/LIPIcs.STACS.2014.1/LIPIcs.STACS.2014.1.pdf): Section 1 (the undecidability of reachability for parameterized programs with identities and its proof sketch, and the formulation of the coverability problem for anonymous crowds) and Sections 2–3 (communication mechanisms and complexity results).
- Krzysztof R. Apt and Dexter C. Kozen, "Limits for automatic verification of finite-state concurrent systems", *Information Processing Letters* 22(6), 1986, pp. 307–309, doi:[10.1016/0020-0190(86)90071-2](https://doi.org/10.1016/0020-0190(86)90071-2), the classical reference on limits of automatic verification for parameterized finite-state systems; not read, cited beside the source above.
