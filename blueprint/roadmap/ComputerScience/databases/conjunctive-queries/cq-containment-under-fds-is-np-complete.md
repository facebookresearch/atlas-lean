# Containment of conjunctive queries under functional dependencies is NP-complete

For a set $\Sigma$ of integrity constraints and conjunctive queries $q, q'$, write $q \subseteq_\Sigma q'$ when
$q(D) \subseteq q'(D)$ for every (finite) database $D$ that satisfies $\Sigma$. The problem of deciding, for conjunctive queries $q, q'$ and a set $\Sigma$ of
functional dependencies, whether $q \subseteq_\Sigma q'$ is NP-complete. A witness is a homomorphism from $q'$ to the
result of chasing the atoms of $q$ with $\Sigma$, which identifies terms as the dependencies dictate, computes in
polynomial time and either fails (then $q \subseteq_\Sigma q'$ holds trivially) or yields a set of atoms satisfying
$\Sigma$.

## Depends on

- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)
- [Functional dependency](../functional-dependencies/fd.md)
- [NP-complete decision problems](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Containment of tableau queries under functional and join dependencies via the chase](../dependencies-and-the-chase/containment-under-fds-and-jds-via-the-chase.md)
- [Chandra-Merlin containment criterion](../../not-yet-classified/conjunctive-queries/contained-iff-hom.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, the problem CQ-Containment-FD, Theorem 17.2 (p. 132), Theorem 17.3 and Corollary 17.4 (p. 133).
