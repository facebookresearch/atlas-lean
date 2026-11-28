# Reachability for Petri nets with two inhibitor arcs is undecidable

Adding inhibitor arcs, which allow a transition to fire only when a given place is empty, makes the reachability problem for Petri nets undecidable as soon as the net has two inhibitor arcs; with a single inhibitor arc it stays decidable.

**Inhibitor nets.** An inhibitor net is an ordinary [Petri net](../../../place-transition-petri-nets.md) (all arcs of weight $1$, as in the survey's Section 2) together with a set of inhibitor arcs, each a pair $(p, t)$ of a place and a transition. A transition $t$ is enabled at a marking $M$ if it is enabled in the underlying Petri net and $M(p) = 0$ for every inhibitor arc $(p, t)$; firing changes the marking as in the underlying net.

**Reachability problem.** Given an inhibitor net with initial marking $M_0$ and a marking $M$, decide whether $M$ is reachable from $M_0$.

**Theorem (Hack).** The reachability problem is undecidable for ordinary Petri nets with at least two inhibitor arcs.

The bound counts the inhibitor arcs of the whole net, and the net and both markings are the input. Reinhardt showed that reachability is decidable for nets with only one inhibitor arc, as the survey below reports.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

An inhibitor arc is an exact test for zero, which ordinary nets cannot perform. A two-counter machine is simulated by a net with one place per control state and one place per counter; routing all zero tests of a counter through a single test transition (the requesting state leaves a return token in an auxiliary place) needs one inhibitor arc per counter, hence two in all. Halting becomes reachability of the marking with one token in the halting state and empty counters. The survey credits the theorem to Hack's thesis; this sketch is the standard idea, not a quotation of it. A good expansion follows a source that proves the theorem with the bound of two inhibitor arcs and links the results its proof uses.

## Sources

- Javier Esparza and Mogens Nielsen, "Decidability issues for Petri nets: a survey", *Journal of Information Processing and Cybernetics (EIK)* 30(3):143–160, 1994; read as arXiv:2411.01592v1, <https://arxiv.org/abs/2411.01592v1>: Section 3, paragraph "Reachability", of arXiv:2411.01592v1, which states the result and credits it to Hack's thesis.
- Fernando Rosa-Velardo and David de Frutos-Escrig, "Decidability and complexity of Petri nets with unordered data", *Theoretical Computer Science* 412(34):4439–4451, 2011, doi:10.1016/j.tcs.2011.05.007; read in the authors' open-access copy at <https://antares.sip.ucm.es/frosa/docs/TCS11.pdf>: Section 4 of that copy, which defines inhibitor nets as above and restates the result.
