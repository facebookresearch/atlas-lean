# Linearizability of unboundedly concurrent finite-state libraries is undecidable

For libraries whose methods are finite automata over finite-domain shared memory, called by an unbounded number of threads, deciding whether every execution is linearizable with respect to a regular sequential specification is undecidable, even though control-state reachability is decidable for such systems.

**Setting (Bouajjani, Emmi, Enea and Hamza).** A *method* is a finite automaton whose transitions change a method-local state together with a valuation of finitely many finite-domain shared variables, with initial and final local states; a *library* $L$ is a finite set of methods. The *most general client* repeatedly calls arbitrary methods of $L$ with arbitrary initial local states. In the *unbounded concurrent system* $L[C]$, arbitrarily many threads run copies of a client $C$ concurrently, each executing at most one library method at a time; a trace records the call, internal and return actions of the threads. An *operation* is the subsequence of actions of one method invocation by one thread; it is *completed* if it ends with a return and *pending* otherwise. A *specification* $S$ is a regular language over symbols $M[m_0, m_f]$, one for each method $M$ with initial and final local states $m_0, m_f$. Extending [linearizability](linearizable.md) to traces with pending operations, a trace $\tau$ is *$S$-linearizable* if some permutation of $\tau$ that preserves the order of same-thread operations and of non-overlapping operations whose first operation is completed, and that is *serial*, so that no two of its operations overlap, pending ones included, has a completion whose sequence of operation symbols belongs to $S$; the completion keeps the completed operations of that sequence in order and, for each pending operation, either deletes it or appends a return to it in its place in the sequence (Section 2.1, Definition 2). A library is $S$-linearizable if every trace of $L$ under the most general client is.

**Theorem (Bouajjani, Emmi, Enea and Hamza).** The linearizability problem for unbounded concurrent systems with regular specifications is undecidable: given a library $L$ and a regular specification $S$, it is undecidable whether $L$ is $S$-linearizable.

In contrast, the same paper shows that conflict serializability and static linearizability (with fixed linearization points) are EXPSPACE-complete for such systems, and that linearizability restricted to traces with a bounded number of barriers is decidable; a later paper of the same authors reduces linearizability for several fixed data-type specifications to control-state reachability.

## Depends on

- [Linearizable histories](linearizable.md)
- [Sequential specifications](seq-spec.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

From a counter machine $A$ and a target state, the authors build a library $L_A$ with a method $T[t]$ for each transition $t$ and methods $I[c]$, $D[c]$, $Z[c]$ for incrementing, decrementing and zero-testing each counter $c$, and a regular specification $S_A$. Using rendezvous synchronization between concurrently running operations, the library allows only traces whose overlapping $T[\cdot]$ operations follow a valid sequence of transitions of $A$, with each increment matched to a later decrement. The specification accepts linearizations that either do not reach the target state or pass a zero test while the counter is nonzero; what the proof needs is that every trace of $L_A$ with a bad zero test has some ordering that $S_A$ accepts, not that $S_A$ recognizes every such ordering (Section 5, Lemma 5). Then $L_A$ is not $S_A$-linearizable if and only if $A$ reaches the target state.

## Sources

- Ahmed Bouajjani, Michael Emmi, Constantin Enea and Jad Hamza, "Verifying Concurrent Programs against Sequential Specifications", Programming Languages and Systems (ESOP 2013), Lecture Notes in Computer Science, pp. 290–309, 2013, <https://doi.org/10.1007/978-3-642-37036-6_17>; Section 2 (unbounded concurrent systems, Definition 2 of linearizability) and Theorem 3 with Section 5 ("Undecidability of Linearizability in the General Case"), read in the publisher's open-access copy at <https://link.springer.com/content/pdf/10.1007/978-3-642-37036-6_17.pdf>.
- Ahmed Bouajjani, Michael Emmi, Constantin Enea and Jad Hamza, "On reducing linearizability to state reachability", Information and Computation 261, pp. 383–400, 2018, <https://doi.org/10.1016/j.ic.2018.02.014>; the abstract and introduction, which recall the undecidability, read in arXiv:1502.06882v2, <https://arxiv.org/abs/1502.06882v2>.
