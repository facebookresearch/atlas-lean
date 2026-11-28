# Finite satisfiability of first-order queries over unary conjunctive views with inequalities is undecidable


Allowing inequalities in the bodies of unary conjunctive views makes finite satisfiability of first-order queries over those views undecidable, although it is decidable when the view bodies are plain conjunctive queries. The source states the same undecidability for recursive unary conjunctive views.

**Theorem (Bailey, Dong and To).** The following problem is undecidable: given a relational vocabulary $\sigma$, a finite set $\mathcal{V}$ of unary conjunctive$^{\neq}$ views over $\sigma$ (conjunctive bodies with inequality atoms allowed) and a first-order sentence built from atoms $V(x)$, $V \in \mathcal{V}$, by $\neg$, $\wedge$ and $\exists$, is the sentence finitely satisfiable, that is, true in some finite $\sigma$-structure?

This is the finite-model argument in the proof sketch of Theorem 5.1 of the source, not the statement of Theorem 5.1, which reads "Satisfiability is undecidable" for satisfiability over all structures, finite or infinite (the two notions are distinguished in Section 2.1). The sketch, recalled below, checks local conditions on the successor relation, which force a chain from the first to the last element in a finite structure but not in an infinite one, so it establishes the finite version stated here and leaves a gap for infinite structures.

The vocabulary and the views are part of the input. The paper states the same undecidability for unary conjunctive$^{\mathrm{rec}}$ views, whose bodies are conjunctive queries without inequality but whose definitions may be recursive (its Theorem 5.4, with a proof sketch adapting the argument below), and recalls from earlier work that views with safe negation also give undecidability.

## Depends on

- [First-order queries over unary conjunctive views](first-order-unary-conjunctive-view-queries.md)
- [Conjunctive queries with inequalities](../conjunctive-queries/conjunctive-queries-with-inequalities.md)
- [Datalog programs and the immediate consequence operator](../datalog/datalog-programs-and-the-immediate-consequence-operator.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from halting of two-counter machines started with both counters zero. A database stores a successor relation $\mathit{succ}$, unary relations $\mathit{zero}$ and $\mathit{last}$ marking the endpoints, one unary relation per control state and a relation $\mathit{config}(t, s, c_1, c_2)$ recording the computation. Unary views with inequalities, together with first-order conditions over them, check local conditions: $\mathit{succ}$ is functional, injective and loop-free, $\mathit{zero}$ has no predecessor and $\mathit{last}$ no successor, every other element of $\mathit{succ}$ has a predecessor, every element with a predecessor has a successor or is $\mathit{last}$, the configuration at $\mathit{zero}$ is the initial one ($\mathit{goodconfigzero}$), consecutive configurations follow the transition function, the halting state occurs ($\mathit{halt}$), and every element whose configuration is not halting has a successor carrying a configuration ($\mathit{hasconfignext}$). In a finite structure these conditions force a chain from $\mathit{zero}$ to $\mathit{last}$ (unrelated cycles are allowed), and since $\mathit{last}$ has no successor, $\mathit{hasconfignext}$ makes the configuration at $\mathit{last}$ halting; so the chain from $\mathit{zero}$ carries a halting run, and the sentence is finitely satisfiable exactly when the machine halts. The check $\mathit{halt}$ alone would not suffice: an unrelated cycle could carry a halting configuration while the chain from $\mathit{zero}$ stops in a non-halting one. In an infinite structure the conditions do not force a chain: an infinite ray from $\mathit{zero}$ can carry a non-halting run, every configuration on it having a successor, while $\mathit{last}$ lies outside $\mathit{succ}$. Without inequalities the chain conditions cannot be stated; for recursive views a view $\mathit{conn\_zero}$ defined by $\mathit{conn\_zero}(x) \leftarrow \mathit{zero}(x)$ and $\mathit{conn\_zero}(x) \leftarrow \mathit{conn\_zero}(y), \mathit{succ}(y, x)$ expresses that $\mathit{last}$ is reachable from $\mathit{zero}$ instead, which, with $\mathit{hasconfignext}$, also excludes such infinite models.

## Sources

- James Bailey, Guozhu Dong and Anthony Widjaja To, "Logical Queries over Views: Decidability and Expressiveness", ACM Transactions on Computational Logic 11(2), pp. 1–35, 2010, <https://doi.org/10.1145/1656242.1656243>; Theorem 5.1 (main statement), Theorem 5.4 (recursive views) and their proofs in Section 5 of arXiv:0803.2559v1 (the copy read), <https://arxiv.org/abs/0803.2559v1>.
