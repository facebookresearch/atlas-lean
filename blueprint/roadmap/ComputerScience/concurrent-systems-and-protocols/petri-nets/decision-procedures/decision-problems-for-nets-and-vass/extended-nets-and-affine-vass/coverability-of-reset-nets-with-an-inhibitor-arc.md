# Coverability of reset nets with one inhibitor arc is undecidable

Coverability is decidable for Petri nets with reset arcs, but adding a single inhibitor arc, which lets one transition fire only when one place is empty, makes it undecidable.

**Reset nets with one inhibitor arc.** A reset net $N = (S, T, F, \mathbf{m}_0)$ has finite sets $S$ of places and $T$ of transitions, an initial marking $\mathbf{m}_0 \in \mathbb{N}^S$ and $F = \langle I, O, Z \rangle$ assigning to each transition $t$ multisets $I(t), O(t)$ of places and a set $Z(t) \subseteq S$ of reset places. $t$ is enabled at $\mathbf{m}$ if $I(t) \le \mathbf{m}$; firing it yields $\mathbf{m}'$ obtained by subtracting $I(t)$, setting every place of $Z(t)$ to $0$, and adding $O(t)$. A reset net with one inhibitor arc additionally has one pair $(t, p) \in T \times S$, and $t$ is enabled at $\mathbf{m}$ only if, in addition, $\mathbf{m}(p) = 0$. With all $Z(t)$ empty and no inhibitor arc this is a [place/transition Petri net](../../../place-transition-petri-nets.md).

**Theorem.** The coverability problem for reset nets with one inhibitor arc (given $N$ and a marking $\mathbf{m}$, is some marking $\mathbf{m}' \ge \mathbf{m}$ reachable from $\mathbf{m}_0$?) is undecidable.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof, attributed to Laurent Van Begin, reduces from the problem whether a two-counter machine reaches a given control location $l_f$ with both counters zero. The net has a place for each control location, places $c_1, c_2$ for the counters, a place $\mathit{cnt}$ incremented and decremented together with the counters, and a place $\mathit{tocov}$. A zero test on $c_j$ has an ordinary transition for the else-branch and, for the then-branch, a transition that resets $c_j$; a reset that removes tokens is a wrong guess, after which $\mathit{cnt}$ holds strictly more tokens than $c_1$ and $c_2$ together. The only inhibitor arc lets the transition from $l_f$ to $\mathit{tocov}$ fire only when $\mathit{cnt}$ is empty, so the marking $[\mathit{tocov}]$ is coverable iff $(l_f, 0, 0)$ is reachable. Without the inhibitor arc coverability is decidable for reset nets, by the well-structured transition system argument of Dufourd, Finkel and Schnoebelen, while their reachability and boundedness are undecidable.

## Sources

- Pierre Ganty and Rupak Majumdar, "Algorithmic verification of asynchronous programs", *ACM Transactions on Programming Languages and Systems* 34(1), Article 6, 48 pages, 2012, <https://doi.org/10.1145/2160910.2160915>; read as arXiv:1011.0551v3, <https://arxiv.org/abs/1011.0551v3>: the definition of reset nets with one inhibitor arc and the coverability theorem in Section 7.6 (reset nets and the decidability of their coverability are recalled in Section 7.3).
- Catherine Dufourd, Alain Finkel and Philippe Schnoebelen, "Reset nets between decidability and undecidability", *Automata, Languages and Programming (ICALP 1998)*, Lecture Notes in Computer Science 1443, pages 103-115, Springer, 1998, <https://doi.org/10.1007/BFb0055044>: decidability of coverability and undecidability of reachability and boundedness for reset nets, as recalled in Section 7.3 of the version of the first source read.
