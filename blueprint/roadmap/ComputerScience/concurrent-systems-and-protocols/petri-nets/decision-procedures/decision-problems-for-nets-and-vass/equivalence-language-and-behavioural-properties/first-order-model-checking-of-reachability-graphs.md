# First-order model checking of Petri net reachability graphs is undecidable

Model checking a first-order formula about the one-step relation of the reachability graph of a Petri net, with no labels on transitions and no propositions on markings, is undecidable already for one fixed formula with two variables; so is the same problem for the reachability relation.

**Setting (Darondeau, Demri, Meyer and Morvan).** A [Petri net](../../../place-transition-petri-nets.md) $\mathcal{N}$ with initial marking $M_0$ induces its *unlabelled reachability graph* $\mathrm{URG}(\mathcal{N})$: its domain is the set $D$ of markings reachable from $M_0$, with the relations $M \to M'$ if $M'$ results from $M$ by firing one transition, its reflexive-transitive closure $\to^*$, its transitive closure $\to^+$, the unary predicate $\mathit{init} = \{M_0\}$ and equality. For a set $\mathtt{P}$ of these predicates, $\mathrm{FO}(\mathtt{P})$ is first-order logic over the predicates in $\mathtt{P}$ only, and the *model-checking problem* $\mathrm{MC}(\mathrm{FO}(\mathtt{P}), \mathrm{URG})$ asks, given a Petri net $\mathcal{N}$ and a sentence $\varphi$ of $\mathrm{FO}(\mathtt{P})$, whether $\mathrm{URG}(\mathcal{N}) \models \varphi$.

**Theorem (Darondeau, Demri, Meyer and Morvan).**

1. There is a sentence $\varphi$ of $\mathrm{FO}(\to)$ with two individual variables such that $\mathrm{MC}(\mathrm{FO}(\to), \mathrm{URG})$ restricted to $\varphi$ is undecidable.
2. $\mathrm{MC}(\mathrm{FO}(\to^+), \mathrm{URG})$ and $\mathrm{MC}(\mathrm{FO}(\to^*), \mathrm{URG})$ are undecidable, the former already for a fixed formula.

Model checking $\mathrm{FO}(\to)$ restricted to one variable is decidable, and the same paper derives that no algorithm constructs an automatic graph isomorphic to the unlabelled reachability graph of a Petri net.

## Depends on

- [Reachability set and reachability graph](../../../reachability-set-and-reachability-graph.md)
- [Place/transition Petri nets](../../../place-transition-petri-nets.md)
- [Decidability by multi-stack machines](../../../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Equality of reachability sets of Petri nets is undecidable](marking-equivalence-is-undecidable.md)

## Expansion

The proofs reduce the equality problem for the reachability sets of two Petri nets with the same places (Hack). From nets $\mathcal{N}_1$ and $\mathcal{N}_2$ the authors build a net whose reachability graph contains the reachable markings of both, marked by a control place, together with gadgets that prolong every reachable marking of $\mathcal{N}_1$ or $\mathcal{N}_2$ to a deadlock, entered from the $\mathcal{N}_1$ side through a marking with a successor that has a self-loop and from the $\mathcal{N}_2$ side through a marking without one. A fixed formula, using the test $\exists y\,(x \to y \wedge y \to y)$, states that every deadlock has a predecessor that passes this test and one that fails it; this holds exactly when the two reachability sets coincide. Recycling variables brings the formula down to two variables. For $\to^+$ and $\to^*$ the authors adapt the gadgets, since self-loops are no longer directly identifiable.

## Sources

- Philippe Darondeau, Stéphane Demri, Roland Meyer and Christophe Morvan, *Petri Net Reachability Graphs: Decidability Status of First Order Properties*, Logical Methods in Computer Science 8(4), 2012, https://doi.org/10.2168/LMCS-8(4:9)2012; the definition of unlabelled reachability graphs and of the logic, the corollary and the theorem on $\mathrm{FO}(\to)$, and the corollaries on $\mathrm{FO}(\to^+)$ and $\mathrm{FO}(\to^*)$, read in arXiv:1210.2972v2. Locators in arXiv:1210.2972v2: Theorem 2.2, Corollary 3.2, Theorem 3.3, Corollary 3.4, Corollary 4.2 and Propositions 3.5 and 4.3.
