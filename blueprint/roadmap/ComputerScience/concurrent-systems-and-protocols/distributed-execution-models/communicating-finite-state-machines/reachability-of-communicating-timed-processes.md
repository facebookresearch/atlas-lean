# Reachability of communicating timed processes over most topologies is undecidable

Finite-state processes with local clocks communicating over unbounded FIFO channels have undecidable reachability unless the communication graph is a polyforest. In discrete time, reachability is decidable exactly for polyforests with at most one channel tested for emptiness per connected component; in dense time, two testable channels in a connected topology already make it undecidable.

**Setting (Clemente, Herbreteau, Stainer and Sutre).** A *topology* $T = \langle P, C, E \rangle$ is a directed graph with a finite set of processes $P$ and channels $C \subseteq P \times P$, together with a set $E \subseteq C$ of channels whose emptiness the receiver can test. It is *weakly connected* if its underlying undirected graph is connected, and a *polyforest* if it is a directed acyclic graph with no undirected cycle. A system of communicating timed processes over $T$ has, for each process, a labeled transition system whose actions are sends $c!m$ on outgoing channels, receives $c?m$ from incoming channels, emptiness tests $c == \varepsilon$ on incoming testable channels, internal actions, and delay actions from a delay domain $D$. Delay actions are performed by all processes simultaneously, all other actions by one process at a time; channel contents are FIFO words over a finite message set. In *communicating tick automata* (discrete time) each process has finitely many states and $D = \{\tau\}$ is a single tick; in *communicating timed automata* (dense time) each process is a timed automaton over its local clocks, with guards comparing clocks to natural numbers, and $D = \mathbb{R}_{\ge 0}$. The *reachability problem* asks whether the system has a run from initial to final local states that ends with all channels empty. In the source's semantics the initial and final states of a timed automaton are its initial and final locations with every clock zero, so for communicating timed automata a run must also start and end with every clock zero; this prevents time from elapsing in final locations, which the reduction from tick automata to timed automata needs (Section 4, before Theorem 6).

**Theorem (Clemente, Herbreteau, Stainer and Sutre).**

1. Given a topology $T$, reachability for systems of communicating tick automata over $T$ is decidable if and only if $T$ is a polyforest with at most one testable channel in each weakly connected component; it is undecidable for every other topology.
2. Given a weakly connected topology $T$ with two testable channels, reachability for systems of communicating timed automata over $T$ is undecidable.

For dense time without emptiness tests, the same paper shows reachability decidable exactly on polyforests. Undecidability on non-polyforest topologies holds already without time, for communicating finite-state machines.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Timed Büchi automata and timed regular languages](../../../../TheoryOfComputation/omega-automata-and-games/timed-automata/timed-buchi-automata.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proofs are topology-preserving reductions between communicating tick automata and communicating counter automata. Synchronized ticks are implemented by broadcasting a tick message, so that each channel can simulate a counter and each emptiness test a zero test; conversely, counters can be implemented by channels. On a connected topology with two testable channels this yields a system equivalent to a two-counter machine, so reachability there is undecidable. Discrete time reduces to dense time over the same topology by forcing every process to let exactly one time unit elapse at each tick, which transfers the undecidability to timed automata. The decidable direction of clause 1 reduces reachability over a polyforest with at most one testable channel per component to reachability for counter automata with zero tests on only one counter, which is decidable (Reinhardt; Bonnet), and the necessity of polyforests uses the undecidability of reachability for communicating finite-state machines on every non-polyforest topology, even without ticks (Pachl; La Torre, Madhusudan and Parlato), both as cited in the proof of Theorem 3. A good expansion links pages for these two results.

## Sources

- Lorenzo Clemente, Frédéric Herbreteau, Amelie Stainer and Grégoire Sutre, "Reachability of Communicating Timed Processes", Foundations of Software Science and Computation Structures (FoSSaCS 2013), Lecture Notes in Computer Science, pp. 81–96, 2013, <https://doi.org/10.1007/978-3-642-37075-5_6>; Definitions 1 and 2, the definition of polyforests, the semantics of timed automata and the paragraph "From tick automata to timed automata" in Section 4, Theorem 3 (clause 1 above), Theorem 5 and Theorem 6 (clause 2 above) of arXiv:1209.0571v2, read at <https://arxiv.org/abs/1209.0571v2>.
