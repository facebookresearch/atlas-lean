# Complexity of certain answers to first-order queries

Consider first-order queries $q$ evaluated over incomplete instances $I$ with nulls, over a countably infinite set of
constants as in [open-world semantics and certain answers with nulls](open-world-semantics-and-certain-answers-with-nulls.md),
and the problem of deciding $\bar a \in \mathrm{cert}_*(q, I)$. Hardness is under polynomial-time many-one reductions.

1. Under the closed-world semantics the problem is coNP-complete in data complexity (for each fixed $q$ it is in coNP,
   and it is coNP-hard for some fixed $q$) and PSPACE-complete in combined complexity.
2. Under the open-world semantics the problem is undecidable in combined complexity.

For the fixed-query lower bound, a graph maps to an incomplete instance on which a proper 3-coloring gives a valuation
making a fixed Boolean query false, so 3-colorability reduces to non-certainty and non-3-colorability to certainty,
which is coNP-hard. Combined-complexity hardness under the closed-world semantics reduces from evaluation of
first-order queries on databases without nulls, which is PSPACE-complete. The open-world lower bound takes the empty
incomplete instance, on which a Boolean query $\varphi$ is certain exactly when it is finitely valid, and $\varphi$ is
finitely valid if and only if $\neg\varphi$ is not finitely satisfiable.

## Depends on

- [Open-world semantics and certain answers with nulls](open-world-semantics-and-certain-answers-with-nulls.md)
- [Relational calculus and domain independence](../relational-calculus/relational-calculus-and-domain-independence.md)
- [Polynomial space for decision problems](../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/pspace.md)
- [The class coNP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/co-np.md)
- [Polynomial-time many-one reduction](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md)

## Proof depends on

- [3-COLOR is NP-hard](../../../TheoryOfComputation/np-completeness/graph-coloring-and-partitioning/graph-3-coloring/part-09/col3-dec-np-hard.md)
- [Data, expression and combined complexity of query evaluation](../query-language-expressiveness/data-expression-and-combined-complexity-of-query-evaluation.md)
- [Satisfiability of relational calculus queries is undecidable](../query-language-expressiveness/satisfiability-of-relational-calculus-queries-is-undecidable.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Theorem 39.6 and its proof (pp. 371–373).
