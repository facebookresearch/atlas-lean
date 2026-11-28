# Reachability for Petri nets with two reset, transfer or doubling arcs is undecidable

Reachability becomes undecidable for Petri nets extended with only two reset arcs, two transfer arcs or two doubling arcs, which empty a place, move all its tokens or double them when a transition fires.

**Extended arcs.** Consider a [Petri net](../../../place-transition-petri-nets.md) in which some arcs carry, instead of a constant weight, the current number of tokens of a place. When a transition $t$ fires at marking $M$:

- a *reset arc* from $t$ to a place $p$ removes all $M(p)$ tokens from $p$;
- a *transfer arc* from $p$ through $t$ to a place $p'$ removes all $M(p)$ tokens from $p$ and adds them to $p'$;
- a *doubling arc* from $t$ to $p$ adds $M(p)$ tokens to $p$.

A *reset Petri net* has ordinary arcs and reset arcs, a *transfer Petri net* ordinary arcs and transfer arcs, and a *double Petri net* ordinary arcs and doubling arcs. The reachability problem asks, given such a net with initial marking $M_0$ and a marking $M$, whether $M$ is reachable from $M_0$.

**Theorem (Dufourd, Finkel and Schnoebelen).** Reachability is undecidable for double Petri nets, reset Petri nets and transfer Petri nets having two extended (doubling, reset or transfer) arcs (Theorem 11).

Reset Petri nets were introduced by Araki and Kasami. Since reachability is decidable for nets with one inhibitor arc, it is also decidable for nets with at most one reset arc or one transfer arc, so two is the threshold for these two extensions; the source conjectures that reachability is decidable with one doubling arc.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Reachability for Petri nets with two inhibitor arcs is undecidable](reachability-with-two-inhibitor-arcs.md)

## Expansion

The proof reduces reachability for nets with inhibitor arcs. Each place $p$ tested by an inhibitor arc gets a twin place $p'$ that receives and loses tokens exactly as $p$ does, and each inhibitor arc from $p$ to $t$ is replaced by a reset arc from $t$ to $p'$. As long as the simulation is faithful, $p$ and $p'$ hold the same number of tokens. Firing $t$ while $p$ is nonempty empties $p'$ but not $p$, and this imbalance can never be repaired. Hence a marking $M$ is reachable in the inhibitor net iff its extension with $M(p') = M(p)$ is reachable in the reset net. Replacing the reset arc by a transfer arc from $p'$ to a fresh dummy place, or by a doubling arc from $t$ to $p'$ (where imbalance means $p'$ has more tokens), gives the other two cases. Two inhibitor arcs thus become two extended arcs.

## Sources

- Catherine Dufourd, Alain Finkel and Philippe Schnoebelen, "Reset nets between decidability and undecidability", in *Automata, Languages and Programming (ICALP 1998)*, Lecture Notes in Computer Science 1443, Springer, 1998, pp. 103–115, doi:10.1007/BFb0055044; read in the authors' open-access copy at <http://www.lsv.fr/Publis/PAPERS/PDF/DFS-icalp98.pdf>: Sections 2 and 3 (G-nets and the families of reset, transfer and double Petri nets), Theorem 11 and the remark after it, of that copy.
