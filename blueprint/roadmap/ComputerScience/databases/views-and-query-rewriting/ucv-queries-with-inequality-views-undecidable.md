# Satisfiability of first-order queries over unary conjunctive views with inequalities is undecidable

Allowing inequalities in the bodies of unary conjunctive views makes satisfiability of first-order queries over those views undecidable, although it is decidable when the view bodies are plain conjunctive queries. The same holds for recursive unary conjunctive views.

**Theorem (Bailey, Dong and To).** The following problem is undecidable: given a relational vocabulary $\sigma$, a finite set $\mathcal{V}$ of unary conjunctive$^{\neq}$ views over $\sigma$ (conjunctive bodies with inequality atoms allowed) and a first-order sentence built from atoms $V(x)$, $V \in \mathcal{V}$, by $\neg$, $\wedge$ and $\exists$, is the sentence satisfiable, that is, true in some $\sigma$-structure, finite or infinite?

The vocabulary and the views are part of the input. The paper states the same undecidability for unary conjunctive$^{\mathrm{rec}}$ views, whose bodies are conjunctive queries without inequality but whose definitions may be recursive (its Theorem 5.4, with a proof sketch adapting the argument below), and recalls from earlier work that views with negated atoms also give undecidability.

## Depends on

- [First-order queries over unary conjunctive views](first-order-unary-conjunctive-view-queries.md)
- [Conjunctive queries with inequalities](../conjunctive-queries/conjunctive-queries-with-inequalities.md)
- [Datalog programs and the immediate consequence operator](../datalog/datalog-programs-and-the-immediate-consequence-operator.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The reduction is from halting of two-counter machines started with both counters zero. A database stores a successor relation $\mathit{succ}$, constants $\mathit{zero}$ and $\mathit{last}$, one unary relation per control state and a relation $\mathit{config}(t, s, c_1, c_2)$ recording the computation. Unary views with inequalities, together with first-order conditions over them, check that each element of $\mathit{succ}$ has at most one successor and one predecessor, that $\mathit{succ}$ contains a chain from $\mathit{zero}$ to $\mathit{last}$ (unrelated cycles are allowed), that consecutive configurations follow the transition function, and that the halting state occurs. The resulting sentence is satisfiable exactly when the machine halts. Without inequalities the chain conditions cannot be stated; for recursive views a view $\mathit{conn\_zero}$ defined by $\mathit{conn\_zero}(x) \leftarrow \mathit{zero}(x)$ and $\mathit{conn\_zero}(x) \leftarrow \mathit{conn\_zero}(y), \mathit{succ}(y, x)$ expresses that $\mathit{last}$ is reachable from $\mathit{zero}$ instead.

## Sources

- James Bailey, Guozhu Dong and Anthony Widjaja To, "Logical Queries over Views: Decidability and Expressiveness", ACM Transactions on Computational Logic 11(2), pp. 1–35, 2010, <https://doi.org/10.1145/1656242.1656243>; Theorem 5.1 (main statement), Theorem 5.4 (recursive views) and their proofs in Section 5 of arXiv:0803.2559v1 (the copy read), <https://arxiv.org/abs/0803.2559v1>.
