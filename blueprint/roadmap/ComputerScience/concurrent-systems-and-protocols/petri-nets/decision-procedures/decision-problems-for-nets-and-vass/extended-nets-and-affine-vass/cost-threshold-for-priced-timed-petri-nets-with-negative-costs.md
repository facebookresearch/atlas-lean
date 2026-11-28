# Cost-threshold reachability for priced timed Petri nets with negative costs is undecidable

Priced timed Petri nets charge for firing transitions and for storing timed tokens over time; with nonnegative costs, the infimum cost of reaching a control-state is computable. Once transitions may have negative costs, deciding whether a control-state is reachable with cost at most a threshold becomes undecidable, already for threshold $0$.

**Setting (Abdulla and Mayr).** A *priced timed Petri net* (PTPN) has a finite set of control-states $Q$, a finite set of places $P$, a finite set of transitions $t = (q_1, q_2, I, R, O)$ with source and target control-states and finite multisets $I, R, O$ of input, read and output arcs, each labeled by a place and a time interval with integer bounds, and a cost function assigning an integer to each place and each transition (natural numbers in most of the source, negative transition costs in its Section 10). A configuration is a control-state with a marking, a finite multiset of tokens $(p, x)$ with real ages $x \ge 0$. A *timed transition* adds the same $x > 0$ to all ages and costs $x \cdot \sum_{p} |M(p)| \cdot \mathrm{cost}(p)$, where $|M(p)|$ is the number of tokens on $p$. A *discrete transition* $t$ changes the control-state from $q_1$ to $q_2$, consumes tokens matching the input arcs, requires tokens matching the read arcs, produces tokens matching the output arcs (with ages in the arcs' intervals), and costs $\mathrm{cost}(t)$. The cost of a computation is the sum of its step costs. In the *cost-threshold problem*, given initial and final control-states $q_{\mathrm{init}}, q_{\mathrm{fin}}$ and a threshold $v \in \mathbb{N}$, one asks whether the infimum of the costs of computations from $q_{\mathrm{init}}$ with all places empty to any configuration with control-state $q_{\mathrm{fin}}$ is at most $v$.

**Theorem (Abdulla and Mayr).** If transitions may have negative integer costs, the cost-threshold problem for priced timed Petri nets is undecidable (Theorem 10.1). This holds even when place costs are nonnegative, transition costs are nonpositive, the threshold is $0$, and clock values are natural numbers (discrete time).

With nonnegative costs on places and transitions, the same paper shows that the infimum cost is computable.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from control-state reachability for two-counter Minsky machines. Each counter is a place with storage cost $1$ whose token count is the counter value; increments and decrements add or remove a token at cost $0$. A zero test on counter $c_i$ is simulated by a gadget that lets time pass while both counter places hold tokens, so a cheating test with $c_i$ nonempty incurs a positive cost that the rest of the computation cannot compensate. The unjustified cost charged for the tokens on the other counter $c_{1-i}$ is reimbursed, at most completely, by auxiliary transitions with negative cost. Hence the final control-state is reachable with cost at most $0$ exactly when the counter machine reaches it.

## Sources

- Parosh Aziz Abdulla and Richard Mayr, "Priced Timed Petri Nets", Logical Methods in Computer Science 9(4), 2013, <https://doi.org/10.2168/LMCS-9(4:10)2013>; the definitions of the section "Priced Timed Petri Nets" (model, computations, costs and the priced coverability problem) and the theorem with its proof in the section "Undecidability for Negative Costs" of arXiv:1307.2570v2, read at <https://arxiv.org/abs/1307.2570v2>.
