# Epistemic planning under b-commutativity is undecidable for three or more agents

Plan existence stays undecidable when multi-agent knowledge obeys $b$-commutativity for some $b > 1$, as soon as there are at least three agents, whereas full commutativity, or two agents, makes it decidable.

**Theorem.** For every $n > 2$ and every $b > 1$, the plan existence problem $\mathrm{PlanEx}(\mathcal T_{\mathrm C^b\text{-}\mathrm{S5}}, n)$ for [epistemic planning under $b$-commutativity](epistemic-planning-under-b-commutativity.md) is undecidable.

The proof adapts the reduction of Aucher and Bolander (IJCAI 2013), as the source states.

## Depends on

- [Epistemic planning under b-commutativity](epistemic-planning-under-b-commutativity.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The source adapts Aucher and Bolander's reduction from the halting problem of two-counter (Minsky) machines to plan existence in $\mathrm{S5}_n$. It proves the case $b = 2$, $n = 3$; since $\mathrm C^2$-$\mathrm{S5}_3$-models are also $\mathrm C^b$-$\mathrm{S5}_n$-models for larger $b$ and $n$, the result follows for all $n \ge 3$ and $b \ge 2$. The proof encodes integers and machine configurations, builds a finite set of actions implementing the transition function, and turns halting into a planning task. In Aucher and Bolander's encoding integers are chains of worlds alternately linked by two agents; axiom $\mathrm C^2$ would collapse such chains. The source therefore builds "meta-chains" whose meta-worlds are alternately linked by two different relations, which needs a third agent. Its proof in the arXiv version is a sketch.

The same source shows that plan existence is decidable for $\mathrm C$-$\mathrm{S5}_n$ for every $n > 1$ (full commutativity bounds the distance between reachable worlds), for $\mathrm C^b$-$\mathrm{S5}_2$ for every $b > 1$, and for weak commutativity.

## Sources

- Alessandro Burigana, Paolo Felli, Marco Montali and Nicolas Troquard, "A Semantic Approach to Decidability in Epistemic Planning", in *ECAI 2023*, Frontiers in Artificial Intelligence and Applications 372, IOS Press, 2023, <https://doi.org/10.3233/FAIA230286>; read as the extended version arXiv:2307.15485v1, <https://arxiv.org/abs/2307.15485v1>: Theorem 5 (undecidability for $n > 2$) and Theorem 4 (decidability for $n = 2$) in Section 4.1, Theorem 3 (decidability under full commutativity) in Section 4, the proof sketch of Theorem 5 there, and its full proof in the appendix, in the numbering of that version.
