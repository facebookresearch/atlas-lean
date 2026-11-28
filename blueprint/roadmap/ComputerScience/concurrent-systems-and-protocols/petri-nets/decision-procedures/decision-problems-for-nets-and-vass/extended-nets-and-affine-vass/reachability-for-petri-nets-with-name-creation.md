# Reachability for Petri nets with name creation is undecidable

In ν-Petri nets, whose tokens carry names that transitions can match, move and freshly create, the reachability problem is undecidable, while coverability, termination and boundedness remain decidable.

**ν-Petri nets.** Fix an infinite set $\mathit{Id}$ of names and a set $\mathit{Var}$ of variables containing an infinite subset $\Upsilon$ of name-creation variables. A *ν-Petri net* is $N = (P, T, F)$ with finite disjoint sets of places $P$ and transitions $T$ and $F : (P \times T) \cup (T \times P) \to \mathit{Var}^{\oplus}$ assigning a finite multiset of variables to each arc, such that for every transition $t$ no variable of $\Upsilon$ occurs on its incoming arcs and every variable on its outgoing arcs outside $\Upsilon$ occurs on its incoming arcs. A *marking* maps each place to a finite multiset of names. A *mode* of $t$ is an injection $\sigma$ from the variables of $t$ to $\mathit{Id}$; $t$ is enabled at $M$ with mode $\sigma$ if $\sigma(F(p,t)) \subseteq M(p)$ for every place $p$ and $\sigma(\nu)$ occurs nowhere in $M$ for every $\nu \in \Upsilon$ of $t$. Firing yields $M'(p) = (M(p) - \sigma(F(p,t))) + \sigma(F(t,p))$.

**Reachability problem.** Given a ν-Petri net, an initial marking $M_0$ and a marking $M$, decide whether $M_0 \to^* M$.

**Theorem (Rosa-Velardo and de Frutos-Escrig).** Reachability is undecidable for ν-Petri nets (Proposition 1). It remains undecidable when modes need not be injective, that is, without inequality checks between names.

Coverability, termination and boundedness are decidable for ν-Petri nets, which are strictly well-structured transition systems (Section 5), but not primitive recursive. A ν-Petri net without name-creation variables can be expanded into an ordinary [Petri net](../../../place-transition-petri-nets.md), so its reachability is decidable.

## Depends on

- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Reachability for Petri nets with two inhibitor arcs is undecidable](reachability-with-two-inhibitor-arcs.md)

## Expansion

An inhibitor net is weakly simulated: each place $p$ gets a companion place $\bar{p}$ holding one token whose name marks the "current" tokens of $p$. Ordinary firings use and produce tokens with that name, while a transition that tests $p$ for zero replaces the name in $\bar{p}$ by a fresh one. The simulation may cheat by testing a nonempty place, but then the tokens left in $p$ carry an old name and can never be removed. So the target marking, encoded with matching names, is reachable in the ν-Petri net iff it is reachable in the inhibitor net, after trying the finitely many possible assignments of names to places.

## Sources

- Fernando Rosa-Velardo and David de Frutos-Escrig, "Decidability and complexity of Petri nets with unordered data", *Theoretical Computer Science* 412(34):4439–4451, 2011, doi:10.1016/j.tcs.2011.05.007; read in the authors' open-access copy at <https://antares.sip.ucm.es/frosa/docs/TCS11.pdf>: Definitions 1, 2 and 3, Proposition 1 and the remark after its proof, Section 4, and Sections 5 and 6 (decidability of coverability, termination and boundedness) of that copy.
