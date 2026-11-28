# Bag containment of Boolean CQs up to any factor 1 + ε is undecidable

For every rational $\varepsilon > 0$, no algorithm decides whether $(1 + \varepsilon)$ times the homomorphism count of one Boolean conjunctive query is at most the count of another on every non-trivial database. For $\varepsilon = 0$ the question becomes bag containment of conjunctive queries on non-trivial databases; the decidability of bag containment of conjunctive queries is open.

**Setting.** Databases are finite relational structures, sets of facts with no repeated fact (bag-set semantics), whose signature may contain constants, among them $\mathfrak{m}$ and $\mathfrak{v}$; a database is non-trivial if $\mathfrak{m} \ne \mathfrak{v}$ holds in it; and for a Boolean conjunctive query $\beta$ without inequalities, $\beta(D) = |\mathrm{Hom}(\beta, D)|$ counts homomorphisms fixing the constants.

**Theorem (Marcinkowski and Ostropolski-Nalewaja).** For each rational $\varepsilon > 0$ the following problem is undecidable: given Boolean conjunctive queries $\beta_s$ and $\beta_b$, does $(1 + \varepsilon) \cdot \beta_s(D) \le \beta_b(D)$ hold for every non-trivial database $D$?

Here $\varepsilon$ is fixed and only the queries are input. Non-triviality is needed: on the one-element database in which every atom holds both counts equal $1$, and $1 + \varepsilon > 1$. Taking $\varepsilon = 1$, the problem whether $\phi_s \vee \phi_s$ is bag-contained in $\phi_b$ on every non-trivial database is undecidable (Corollary 4), and bag containment of Boolean conjunctive queries with at most one inequality each, over all databases, is undecidable (Corollary 5, a result first proved by Marcinkowski and Orda).

## Depends on

- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)
- [Bag semantics of CQs: bag containment and bag equivalence](bag-semantics-of-cqs-bag-containment-and-bag-equivalence.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Some multi-stack machine has an undecidable halting set](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/exists-not-tm2-decidable-tm2-halts-on.md)

## Expansion

The source of undecidability is a variant of Hilbert's tenth problem, with polynomials represented by unions of conjunctive queries as in the work of Ioannidis and Ramakrishnan. The authors' CQ-ization replaces such a union by a single conjunctive query whose homomorphism count on a database depends in a controlled way on the count of the union, which avoids the anti-cheating gadgets of earlier proofs. For Corollary 5, with a fresh unary relation $P$, the queries $\alpha_s = \mathfrak{m} \ne \mathfrak{v} \wedge P(\mathfrak{m}) \wedge P(\mathfrak{v}) \wedge P(z) \wedge P(z')$ and $\alpha_b = P(z) \wedge P(z') \wedge z \ne z'$ satisfy $\alpha_s(D) \le 2\,\alpha_b(D)$ for every $D$, with equality when the only $P$-facts are $P(\mathfrak{m})$ and $P(\mathfrak{v})$, so $2\beta_s \le \beta_b$ on non-trivial databases if and only if $\beta_s \wedge \alpha_s$ is bag-contained in $\beta_b \wedge \alpha_b$.

A good expansion links a page for the CQ-ization of a union of conjunctive queries, with the controlled dependence of its homomorphism count on the count of the union.

## Sources

- Jerzy Marcinkowski and Piotr Ostropolski-Nalewaja, "Bag Semantics Query Containment: The CQ vs. UCQ Case and Other Stories", Proceedings of the ACM on Management of Data 3(5), 24 pages, 2025, <https://doi.org/10.1145/3767711>; Theorem 3 (main statement) with its proof in Section 10, Corollaries 4 and 5 with the proof of Corollary 5 in Section 3, and Section 2 of arXiv:2503.07219v3 (the copy read), <https://arxiv.org/abs/2503.07219v3>.
