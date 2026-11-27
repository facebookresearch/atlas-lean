# Dichotomy for conjunctive queries on tuple-independent probabilistic databases

For every Boolean conjunctive query $q$ (self-joins allowed), computing $p(q)$ on tuple-independent probabilistic
databases either takes polynomial time or is $\#P$-hard. This is the case of a single disjunct in the
[dichotomy for unions of conjunctive queries on tuple-independent probabilistic databases](dichotomy-for-ucqs-on-probabilistic-databases.md), whose safety test decides the side; in
particular $q$ is on the hard side whenever its minimal equivalent query is not hierarchical. A finer criterion for
hierarchical queries announced in the 2007 conference version, based on inversions and erasers, was later withdrawn as
unsound (Appendix A of the journal manuscript) and is not used here.

## Depends on

- [Tuple-independent probabilistic databases and query probability](tuple-independent-probabilistic-databases.md)
- [Hierarchical conjunctive queries](hierarchical-conjunctive-queries.md)
- [$\#P$-complete functions](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/sharp-pcomplete.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)
- [CQ minimization (cores) and UCQ containment](../conjunctive-queries/cq-minimization-and-ucq-containment.md)
- [Dichotomy for unions of conjunctive queries on tuple-independent probabilistic databases](dichotomy-for-ucqs-on-probabilistic-databases.md)

## Proof depends on

- [Conjunctive queries whose minimal equivalent query is not hierarchical are #P-hard on probabilistic databases](non-hierarchical-conjunctive-queries-are-sharp-p-hard.md)

## Sources

- N. Dalvi and D. Suciu, "The dichotomy of probabilistic inference for unions of conjunctive queries", *Journal of the ACM* 59(6), Article 30, 2012, with theorem numbers as in the authors' copy <https://homes.cs.washington.edu/~suciu/jacm-dichotomy.pdf>: Theorem 4.21 (applied to a single conjunctive query) and Appendix A.
- N. Dalvi and D. Suciu, "The dichotomy of conjunctive queries on probabilistic structures", *Proceedings of the 26th ACM Symposium on Principles of Database Systems (PODS)*, 2007, pp. 293–302, Definition 1.2 and Theorem 1.4 (p. 294).
