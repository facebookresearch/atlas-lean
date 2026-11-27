# Containment of conjunctive queries under functional dependencies is NP-complete

For a set $\Sigma$ of integrity constraints and conjunctive queries $q, q'$, write $q \subseteq_\Sigma q'$ when
$q(D) \subseteq q'(D)$ for every (finite) database $D$ that satisfies $\Sigma$. The problem of deciding, for conjunctive queries $q, q'$ and a set $\Sigma$ of
functional dependencies, whether $q \subseteq_\Sigma q'$ is NP-complete. Chasing $q$ with $\Sigma$ identifies terms as the
dependencies dictate, computes in polynomial time and either fails (then $q \subseteq_\Sigma q'$ holds trivially) or
yields a set of atoms that satisfies $\Sigma$ together with the head tuple of $q$ as rewritten by the chase, which may
contain constants, so the pair is a tableau rather than a query of the linked syntax; in that case a witness is a map
that is the identity on constants, sends every atom of $q'$ to a chased atom and maps the head tuple of $q'$ to the
rewritten head tuple. NP-hardness is inherited from containment
of conjunctive queries by taking $\Sigma$ empty.

## Depends on

- [Answers of a conjunctive query](answers-of-a-conjunctive-query.md)
- [Functional dependency](../functional-dependencies/fd.md)
- [NP-complete decision problems](../../../TheoryOfComputation/complexity-classes/mahaney-s-theorem/npcomplete.md)

## Proof depends on

- [Containment of tableau queries under functional and join dependencies via the chase](../dependency-reasoning/containment-under-fds-and-jds-via-the-chase.md)
- [Chandra-Merlin containment criterion](../conjunctive-queries-and-the-chandra-merlin-theor/contained-iff-hom.md)
- [CONJUNCTIVE QUERY CONTAINMENT is NP-complete](../../../TheoryOfComputation/not-yet-classified/part-01/part-10/conjunctive-query-containment/conjunctive-query-containment-np-complet.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, the problem CQ-Containment-FD, Theorem 17.2 (p. 132), Theorem 17.3 and Corollary 17.4 (p. 133).
