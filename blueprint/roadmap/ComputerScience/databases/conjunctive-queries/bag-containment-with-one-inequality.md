# Bag containment with one inequality is undecidable

No algorithm decides, given a Boolean conjunctive query without inequalities and one with at most one inequality, whether the first has at most as many homomorphisms as the second into every database with two distinct designated constants. This lowers the earlier bound of $59^{10}$ inequalities per query to one.

**Setting.** As in [bag containment up to a constant factor](bag-containment-up-to-a-constant-factor.md): databases are finite relational structures over a schema with constants, including $\mathfrak{m}$ and $\mathfrak{v}$; $D$ is non-trivial if $\mathfrak{m}$ and $\mathfrak{v}$ denote different elements; a Boolean conjunctive query $\psi$, possibly with inequality atoms $x \ne x'$ between variables or constants, has value $\psi(D) = |\mathrm{Hom}(\psi, D)|$, where $\ne$ is interpreted as $(V_D \times V_D) \setminus \{(s, s) : s \in V_D\}$ and homomorphisms fix constants.

**Theorem (Marcinkowski and Orda).** The following problem is undecidable: given Boolean conjunctive queries $\psi_s$ without inequalities and $\psi_b$ with at most one inequality, does $\psi_s(D) \le \psi_b(D)$ hold for every non-trivial database $D$?

Since non-triviality can be enforced by adding the atom $\mathfrak{m} \ne \mathfrak{v}$ to $\psi_s$, bag containment of Boolean conjunctive queries with inequalities is undecidable already when each query has at most one inequality; Jayram, Kolaitis and Vee had shown undecidability with $59^{10}$ inequalities. Moving the inequality out of $\psi_b$ instead would settle an open problem: when $\psi_b$ has no inequalities and $\psi_s$ has any number of them, the problem (over all databases) is decidable if and only if bag containment of conjunctive queries without inequalities is decidable.

## Depends on

- [Conjunctive queries with inequalities](conjunctive-queries-with-inequalities.md)
- [Bag semantics of CQs: bag containment and bag equivalence](bag-semantics-of-cqs-bag-containment-and-bag-equivalence.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Bag containment of Boolean conjunctive queries up to a constant factor is undecidable](bag-containment-up-to-a-constant-factor.md)

## Expansion

The theorem follows from the constant-factor version: a combinatorial gadget uses the single inequality in $\psi_b$ to simulate multiplication of the count of $\psi_s$ by the constant $c$, so that $c \cdot \phi_s(D) \le \phi_b(D)$ on non-trivial databases reduces to $\psi_s(D) \le \psi_b(D)$ (Section 3 of the arXiv version).

A good expansion links a page for the gadget of Section 3 that uses one inequality to multiply the count of a query by a constant $c$.

## Sources

- Jerzy Marcinkowski and Mateusz Orda, "Bag Semantics Conjunctive Query Containment. Four Small Steps Towards Undecidability", Proceedings of the ACM on Management of Data 2(2) (PODS 2024), Article 103, 2024, <https://doi.org/10.1145/3651604>; Theorem 3 (main statement), Theorem 5 (equivalence with the inequality-free problem) and Section 3 of arXiv:2503.18003v1, <https://arxiv.org/abs/2503.18003v1>.
- T. S. Jayram, Phokion G. Kolaitis and Erik Vee, "The Containment Problem for Real Conjunctive Queries with Inequalities", Proceedings of the 25th ACM SIGMOD-SIGACT-SIGART Symposium on Principles of Database Systems (PODS 2006), pp. 80–89, 2006, <https://doi.org/10.1145/1142351.1142363>; the earlier bound, not read: the clause rests on Section 1 of the version read of the first source above, which recalls it.
