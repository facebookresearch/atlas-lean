# Containment of unions of conjunctive queries with inequalities is Π2p-complete

The decision problem that asks, for two unions of conjunctive queries with inequalities
$q = q_1 \cup \cdots \cup q_n$ and $q' = q'_1 \cup \cdots \cup q'_m$, whether $q \subseteq q'$ is $\Pi_2^p$-complete.
Containment cannot be tested disjunct by disjunct:
$\exists x \exists y\, E(x, y)$ is contained in the union of $\exists x\, E(x, x)$ and
$\exists x \exists y\, (E(x, y) \wedge x \ne y)$ but in neither disjunct. Instead, with $H_{q_i,q'}$ and $h(q_i^+)$ as in the
[homomorphism criterion for containment of conjunctive queries with inequalities](containment-of-cqs-with-inequalities-via-homomorphic-images.md), taking the constants of $q$ and
$q'$, $q \subseteq q'$ if and only if for every $i$ and every $h \in H_{q_i,q'}$ some $q'_j$ has a homomorphism to
$h(q_i^+)$. Non-containment is decided in $\Sigma_2^p$ by guessing $i$ and $h$ and checking with an NP oracle that no
$q'_j$ maps to $h(q_i^+)$.

## Depends on

- [Conjunctive queries with inequalities](conjunctive-queries-with-inequalities.md)
- [The universal levels of the polynomial hierarchy](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pi-k.md)
- [Polynomial-time many-one reduction](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)
- [Homomorphism criterion for containment of conjunctive queries with inequalities](containment-of-cqs-with-inequalities-via-homomorphic-images.md)

## Proof depends on

- [Containment of conjunctive queries with inequalities is Π2p-complete](containment-of-cqs-with-inequalities-is-pi2p-complete.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Theorem 30.17 (p. 281); its Proposition 30.16, a disjunct-by-disjunct test, fails in the presence of inequalities.
