# Parameterized verification of oblivious robots on a ring is undecidable

Protocols for a fixed number of oblivious mobile robots on rings of unknown size can be written as Presburger formulas over each robot's view of the distances to the others. Whether some ring size and starting configuration lead to a bad configuration is undecidable under the asynchronous scheduler, and the paper's reachability variant is undecidable under all three schedulers.

**Setting (Sangnier, Sznajder, Potop-Butucaru and Tixeuil).** Fix a number $k > 0$ of robots. On a ring of size $n \ge k$ with positions $0, \dots, n-1$ numbered clockwise, a *$(k, n)$-configuration* gives each robot's position. The *view* of a robot lists the clockwise distances between successive robots starting from its next occupied neighbor, a tuple $(d_1, \dots, d_k)$ with $d_1 \ne 0$ and $\sum d_i = n$; the view in the opposite direction is its reversal. A *protocol* is a quantifier-free Presburger formula $\phi(x_1, \dots, x_k)$ such that whenever a view satisfies $\phi$ and differs from its reversal, the reversal does not satisfy $\phi$: a robot moves one step clockwise if its clockwise view satisfies $\phi$, one step counterclockwise if its counterclockwise view does, either way if both views coincide and satisfy $\phi$, and stays otherwise. In the *synchronous* mode all robots act at once; in the *semi-synchronous* mode an arbitrary subset does; in the *asynchronous* mode one robot at a time either looks (records its current view) or moves according to its last recorded view. Ring sizes and configurations are specified by quantifier-free Presburger formulas $\mathtt{Ring}(y)$, $\mathtt{Bad}(x_1, \dots, x_k)$ and $\mathtt{Goal}(x_1, \dots, x_k)$. For a mode $m$, the problem $\mathrm{SAFETY}_m$ asks whether there are a size $n$ satisfying $\mathtt{Ring}$ and a configuration outside $\mathtt{Bad}$ from which a configuration in $\mathtt{Bad}$ is reachable; $\mathrm{REACHABILITY}_m$ asks whether there are a size $n$ satisfying $\mathtt{Ring}$ and a configuration from which no configuration in $\mathtt{Goal}$ is reachable.

**Theorem (Sangnier, Sznajder, Potop-Butucaru and Tixeuil).**

1. For some fixed number of robots ($k = 42$ in the source's proof), $\mathrm{SAFETY}$ in the asynchronous mode is undecidable (Theorem 2).
2. For some fixed number of robots, $\mathrm{REACHABILITY}$ is undecidable in each of the synchronous, semi-synchronous and asynchronous modes (Theorem 3).

The number of robots matters: for $k = 1$ the robot's only view is $(n)$, so it either never moves or reaches every position, and $\mathrm{SAFETY}$ reduces to a Presburger sentence, which is decidable.

When at most one robot can move in any configuration, the three semantics have the same reachable configurations; the same paper shows that safety is decidable in the synchronous and semi-synchronous modes, by reduction to satisfiability of existential Presburger formulas.

## Depends on

- [Decidability by multi-stack machines](../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)
- [Halting is undecidable](../../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Both proofs encode runs of deterministic counter machines: Theorem 2 reduces the halting problem of deterministic two-counter machines, with $k = 42$ robots, and Theorem 3 reduces the repeated reachability problem for deterministic three-counter zero-initializing bounded-strongly-cyclic machines (does an infinite space-bounded run exist?), which the source cites as undecidable. The distances between robots on the ring store the machine's control state and counter values, so that a configuration of the robots of a special "machine-like" shape represents a machine configuration, and the protocol makes the robots move so that successive machine-like configurations follow the machine's transitions. In the asynchronous case, a bad configuration (a collision) becomes reachable from a configuration encoding the initial machine configuration exactly when the machine halts; because the ring size is existentially quantified, a large enough ring holds any finite computation. A good expansion links a page for the undecidability of that repeated reachability problem.

## Sources

- Arnaud Sangnier, Nathalie Sznajder, Maria Potop-Butucaru and Sébastien Tixeuil, "Parameterized verification of algorithms for oblivious robots on a ring", Formal Methods in Computer-Aided Design (FMCAD 2017), pp. 212–219, 2017, <https://doi.org/10.23919/FMCAD.2017.8102262>; journal version Formal Methods in System Design 56, pp. 55–89, 2019, <https://doi.org/10.1007/s10703-019-00335-y>; Section 2 (the formal model, protocols and the three semantics, the two problems), Theorem 2 and Theorem 3 (main statement) of Section 3 with their proofs in Appendices B and C, Theorem 1 (uniquely-sequentializable protocols) of Section 2, and Theorem 4 (decidability of safety in the synchronous and semi-synchronous modes) of arXiv:1706.05193v1, read at <https://arxiv.org/abs/1706.05193v1>.
