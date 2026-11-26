# Complexity of certain answers to first-order queries

Consider first-order queries $q$ evaluated over incomplete instances $I$ with nulls, and the problem of deciding
$\bar a \in \mathrm{cert}_*(q, I)$.

1. Under the closed-world semantics the problem is coNP-complete in data complexity (for each fixed $q$ it is in coNP,
   and it is coNP-hard for some fixed $q$) and PSPACE-complete in combined complexity.
2. Under the open-world semantics the problem is undecidable in combined complexity.

## Depends on

- [Open-world semantics and certain answers with nulls](open-world-semantics-and-certain-answers-with-nulls.md)
- [Relational calculus and domain independence](../relational-calculus/relational-calculus-and-domain-independence.md)
- [The complexity class NP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md)
- [Polynomial space for decision problems](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Theorem 39.6 (p. 371).
