# All-instances termination of the oblivious chase is undecidable

No algorithm decides, for a finite set of single-head tuple-generating dependencies over a ternary signature, whether the oblivious chase terminates on every finite database instance; for the semi-oblivious chase the same problem is undecidable for multi-head TGDs over binary signatures.

**Theorem.** The all-instances termination problem of the [oblivious chase](oblivious-and-semi-oblivious-chase.md) (given a program $\mathcal T$, does the $\mathcal T$-chase terminate on every finite database instance $D$?) is undecidable, and r.e.-hard, already for programs consisting of single-head TGDs over ternary signatures (Theorem 1 of the source). For the semi-oblivious chase the source proves the same undecidability and r.e.-hardness for programs of multi-head TGDs over binary signatures (Theorem 16).

## Depends on

- [Oblivious and semi-oblivious chase termination](oblivious-and-semi-oblivious-chase.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

None.

## Expansion

By the critical-instance lemma, termination on all instances is termination on the one-element instance $D_\Sigma$, so the problem is recursively enumerable and the theorem makes it r.e.-complete. The reduction is from the halting problem of three-counter machines started in the initial state with empty counters. The machine is first encoded as a Conway-style function on natural numbers, and the program $\mathcal T_M$ makes every new element of the chase run its own copy of the computation along the path that leads from the database to it, using only Datalog rules. An element may create a successor only after its computation has reached an atom that exists only in the database; such atoms are never derived. Elements too far from this "well of positivity" can no longer reach it and produce no offspring. The chase on $D_\Sigma$ is then unbounded exactly when $M$ does not halt. The proof applies verbatim to the semi-oblivious chase.

A modification of the program shows that all-instances, all-paths termination of the standard chase is also undecidable; the source notes that this also follows from an earlier reduction of Grahne and Onet. For binary signatures the source proves only EXPSPACE-hardness for the oblivious chase and leaves decidability open; the arXiv version adds that with multi-head TGDs the semi-oblivious problem is undecidable already over binary signatures.

A good expansion links the undecidability of the halting problem for three-counter machines started with empty counters and its Conway-function encoding.

## Sources

- Tomasz Gogacz and Jerzy Marcinkowski, "All-Instances Termination of Chase is Undecidable", in *Automata, Languages, and Programming (ICALP 2014), Part II*, Lecture Notes in Computer Science 8573, Springer, 2014, pp. 293–304, <https://doi.org/10.1007/978-3-662-43951-7_25>; read as arXiv:1401.4840v2, <https://arxiv.org/abs/1401.4840v2>: Theorem 1, its proof in Section 3, Subsection 3.5 on the standard chase, Theorem 2 and Appendix D of that version.
