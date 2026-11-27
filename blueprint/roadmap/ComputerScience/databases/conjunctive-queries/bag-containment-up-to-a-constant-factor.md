# Bag containment of Boolean conjunctive queries up to a constant factor is undecidable

No algorithm decides, given Boolean conjunctive queries $\phi_s, \phi_b$ without inequalities and a natural number $c$, whether $c \cdot \phi_s(D) \le \phi_b(D)$ for every database $D$ with two distinct designated constants, where $\phi(D)$ counts the homomorphisms from $\phi$ to $D$.

**Setting.** A database is a finite relational structure over a schema that may contain constant symbols, among them two constants $\mathfrak{m}$ and $\mathfrak{v}$; a database $D$ is *non-trivial* if $\mathfrak{m}$ and $\mathfrak{v}$ are interpreted by different elements. A query is a Boolean conjunctive query, identified with its canonical structure (its variables and constants as domain, its atoms as facts). Under bag (multiset) semantics the value of a query $\psi$ on $D$ is the natural number

$$
\psi(D) = |\mathrm{Hom}(\psi, D)|,
$$

the number of homomorphisms from the canonical structure of $\psi$ to $D$ that fix every constant.

**Theorem (Marcinkowski and Orda).** The following problem is undecidable: given Boolean conjunctive queries $\phi_s$ and $\phi_b$ without inequalities and a natural number $c$, does $c \cdot \phi_s(D) \le \phi_b(D)$ hold for every non-trivial database $D$?

The non-triviality condition cannot simply be dropped for $c > 1$: on the one-element database in which every atom holds, every query without inequalities has value $1$, so $c \cdot \phi_s(D) > \phi_b(D)$ there. The same paper states that replacing non-triviality by an additive constant keeps the problem undecidable (inputs $\phi_s, \phi_b, c, c'$; question: $c \cdot \phi_s(D) \le \phi_b(D) + c'$ for every $D$) (its Theorem 2). With $c = 1$ and all databases allowed, the question is bag containment of Boolean conjunctive queries, whose decidability the paper describes as open.

## Depends on

- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)
- [Bag semantics of CQs: bag containment and bag equivalence](bag-semantics-of-cqs-bag-containment-and-bag-equivalence.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The reduction is from Hilbert's tenth problem, in a variant that compares two polynomials with natural coefficients at all natural arguments. The database supplies the values of the numerical variables, and the universal quantifier over arguments becomes the universal quantifier over databases. A new encoding writes the evaluation of an entire polynomial as a single conjunctive query; it is faithful only on "correct" databases, and an anti-cheating construction, which uses no inequalities, makes $\phi_b(D)$ large enough on every incorrect non-trivial database. The price of avoiding inequalities is the multiplicative constant $c$.

## Sources

- Jerzy Marcinkowski and Mateusz Orda, "Bag Semantics Conjunctive Query Containment. Four Small Steps Towards Undecidability", Proceedings of the ACM on Management of Data 2(2) (PODS 2024), Article 103, 2024, <https://doi.org/10.1145/3651604>; Theorem 1, Theorem 2 (additive variant) and Section 2 (homomorphism-count semantics) of arXiv:2503.18003v1, <https://arxiv.org/abs/2503.18003v1>.
