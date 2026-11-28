# Bag containment of a Boolean UCQ in a Boolean CQ over non-trivial databases is undecidable

Under bag semantics, where a Boolean query counts homomorphisms, no algorithm decides whether a union of conjunctive queries is contained in a single conjunctive query on every non-trivial database, one in which two designated constants are distinct.

**Setting.** A database is a finite relational structure, a set of facts with no repeated fact (bag-set semantics), whose signature may contain constants, among them $\mathfrak{m}$ and $\mathfrak{v}$; it is *non-trivial* if $\mathfrak{m} \ne \mathfrak{v}$ holds in it. For a Boolean conjunctive query $\phi$ (all variables existentially quantified) and a database $D$, $\phi(D) = |\mathrm{Hom}(\phi, D)|$ is the number of homomorphisms from the canonical structure of $\phi$ to $D$ that fix the constants; for a union $\Phi = \phi_1 \vee \dots \vee \phi_J$, $\Phi(D) = \sum_{j=1}^{J} \phi_j(D)$.

**Theorem (Marcinkowski and Ostropolski-Nalewaja).** The following problem is undecidable: given a Boolean UCQ $\Phi_s$ and a Boolean CQ $\phi_b$, does $\Phi_s(D) \le \phi_b(D)$ hold for every non-trivial database $D$?

The restriction to non-trivial databases matters: on the one-element database in which every atom holds, $\phi_b(D) = 1$ while $\Phi_s(D)$ is the number of disjuncts, so containment over all databases fails for trivial reasons. The number of disjuncts of $\Phi_s$ is unbounded in this theorem; with $\Phi_s = \phi_s \vee \phi_s$ the problem stays undecidable, as a consequence of the result on scaled containment of conjunctive queries.

## Depends on

- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)
- [Bag semantics of CQs: bag containment and bag equivalence](bag-semantics-of-cqs-bag-containment-and-bag-equivalence.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The authors note that the theorem follows from the main result of Marcinkowski and Orda and give a short direct proof: they "CQ-ize" one of the unions of conjunctive queries in the undecidability proof of Ioannidis and Ramakrishnan for bag containment of UCQs, replacing it by a single conjunctive query whose count on a database depends predictably on the count of the union. Both proofs rest on Hilbert's tenth problem.

## Sources

- Jerzy Marcinkowski and Piotr Ostropolski-Nalewaja, "Bag Semantics Query Containment: The CQ vs. UCQ Case and Other Stories", Proceedings of the ACM on Management of Data 3(5), 24 pages, 2025, <https://doi.org/10.1145/3767711>; Theorem 2 and the discussion before it in Section 3, its proof in Section 9, Corollary 4, and the preliminaries of Section 2 of arXiv:2503.07219v3 (the copy read), <https://arxiv.org/abs/2503.07219v3>.
