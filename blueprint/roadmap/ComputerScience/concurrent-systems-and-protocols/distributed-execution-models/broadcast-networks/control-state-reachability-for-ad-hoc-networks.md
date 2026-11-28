# Control-state reachability for ad hoc network protocols is undecidable

In ad hoc networks, identical finite-state processes on an unknown communication graph send selective broadcasts to their neighbors. Whether some initial graph lets some node reach an error state is undecidable, and stays undecidable when the graphs are restricted to diameter at most $k$ for any fixed $k \ge 2$.

**Setting (Delzanno, Sangnier and Zavattaro).** A *process* $\mathcal P = (Q, \Sigma, R, Q_0)$ has finitely many control states $Q$, initial states $Q_0 \subseteq Q$, a message alphabet $\Sigma$ and transitions $R \subseteq Q \times (\{\tau\} \cup \{{!!}a, {??}a : a \in \Sigma\}) \times Q$ (internal action, broadcast of $a$, reception of $a$). A configuration is a finite undirected graph whose vertices are labeled by states of $Q$; initial configurations are all graphs labeled by states of $Q_0$, of any size and shape, and the graph never changes. In one step, either a node performs an internal transition, or a node $v$ broadcasts $a$ by a transition $(L(v), {!!}a, q')$, and simultaneously every neighbor $u$ of $v$ that has a reception $(L(u), {??}a, q'')$ takes one such reception, while the other nodes stay unchanged. The *control-state reachability problem* asks, given $\mathcal P$ and a state $q$, whether some initial configuration reaches a configuration in which some node is in state $q$.

**Theorem (Delzanno, Sangnier and Zavattaro).** The control-state reachability problem for ad hoc network protocols is undecidable. It remains undecidable when configurations are restricted to graphs of diameter at most $k$, for every fixed $k \ge 2$.

In contrast, the problem is decidable over clique graphs (diameter $1$), where it reduces to coverability for broadcast protocols, and over graphs whose maximal-clique graphs have simple paths of bounded length, which include the bounded-path graphs. Coverability stays undecidable for phase-bounded protocols ([coverability of phase-bounded broadcast networks is undecidable](phase-bounded-broadcast-coverability-undecidable.md)).

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Both proofs reduce from the halting problem for two-counter Minsky machines. In a first phase an exploration protocol imposes a logical topology on the unknown graph: for arbitrary topologies, a control node connected to two lists of nodes, one per counter; for diameter $2$, a "butterfly" in which every node of both lists is also adjacent to the control node, with a distinguished first node in each list. The lengths of the lists are guessed in this phase and bound the counter values of the simulation. In the second phase the value of counter $c_i$ is the number of nodes of its list in a nonzero state; the control node simulates the instructions by requests propagated along the lists by broadcasts, which switch one list node between the zero and the nonzero state for increments and decrements and inspect the list for zero tests. The error state is reachable exactly when the machine halts.

## Sources

- Giorgio Delzanno, Arnaud Sangnier and Gianluigi Zavattaro, "Parameterized Verification of Ad Hoc Networks", in *CONCUR 2010 - Concurrency Theory*, Lecture Notes in Computer Science, Springer, 2010, pp. 313–327, doi:[10.1007/978-3-642-15375-4_22](https://doi.org/10.1007/978-3-642-15375-4_22), the original undecidability proof for arbitrary topologies; not read, cited beside the source below.
- Giorgio Delzanno, Arnaud Sangnier and Gianluigi Zavattaro, "Parameterized Verification of Safety Properties in Ad Hoc Network Protocols", in *Proceedings of the First International Workshop on Process Algebra and Coordination (PACO 2011)*, Electronic Proceedings in Theoretical Computer Science 60, 2011, pp. 56–65, doi:[10.4204/EPTCS.60.4](https://doi.org/10.4204/EPTCS.60.4); read in arXiv:1108.1864v1 ([arXiv](https://arxiv.org/abs/1108.1864v1)), cited by section: Section 2 (graphs, ad hoc network protocols, the control-state reachability problem and the statement and proof idea of undecidability for unrestricted topologies), Section 3 (undecidability for bounded diameter) and Section 4 (decidability for bounded-path clique graphs).
