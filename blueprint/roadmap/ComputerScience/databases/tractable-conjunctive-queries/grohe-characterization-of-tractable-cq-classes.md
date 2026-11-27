# Grohe's characterization of tractable classes of conjunctive queries

A core of a conjunctive query $q(\bar x)$ is a query $q'(\bar x)$ whose atoms form a subset of those of $q$, such
that some homomorphism that is the identity on constants maps $q$ to $q'$ fixing $\bar x$ and no query on a proper
subset of the atoms of $q'$ receives such a homomorphism from $q'$; a core of $q$ is equivalent to $q$ and unique up
to renaming of variables. Constants must stay fixed: otherwise $R(a), R(b)$ with constants $a \ne b$ would have the
inequivalent core $R(a)$.

Assume $\mathrm{FPT} \ne \mathrm{W}[1]$. Let $\mathcal C$ be a recursively enumerable class of Boolean conjunctive
queries over relation names of bounded arity, and let $\mathcal C_{\mathrm{core}}$ be the class of cores of the
queries in $\mathcal C$. The following are equivalent:

1. $\mathcal C$-Evaluation (given $q \in \mathcal C$ and a database $D$, decide $D \models q$) is solvable in
   polynomial time;
2. $\mathcal C$-Evaluation, parameterized by the size of $q$, is fixed-parameter tractable;
3. $\mathcal C_{\mathrm{core}}$ has bounded treewidth.

## Expansion

This node states a precise result whose proof the cited textbook only outlines. A good expansion adds pages for the
ingredients of the original proof: minor maps, the encoding of $k$-Clique into a query whose core has a large grid
minor (Grohe, Section 4), and the polynomial-time evaluation of queries of bounded treewidth modulo homomorphic
equivalence (Grohe, Theorem 3.1, credited there to Dalmau, Kolaitis and Vardi).

## Depends on

- [Treewidth of a conjunctive query](treewidth-of-a-conjunctive-query.md)
- [CQ minimization (cores) and UCQ containment](../conjunctive-queries/cq-minimization-and-ucq-containment.md)
- [Fixed-parameter tractable problems](../../../TheoryOfComputation/complexity-classes/parameterized-complexity/fpt.md)
- [The level $\mathrm{W}(t)$ of the W-hierarchy](../../../TheoryOfComputation/complexity-classes/parameterized-complexity/wlevel.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Conjunctive queries whose core has bounded generalized hypertreewidth](cqs-whose-core-has-bounded-ghw-are-tractable.md)
- [Bounded arity makes treewidth and generalized hypertreewidth equivalent for Boolean queries](bounded-arity-treewidth-and-generalized-hypertreewidth.md)
- [Conjunctive-query evaluation parameterized by query size is W[1]-complete](../conjunctive-queries/cq-evaluation-parameterized-by-query-size-is-w1-complete.md)
- [Grid theorem (Robertson–Seymour)](../../../GraphTheory/planar-graphs-and-minors/tree-width/exists-grid-minor-of-not-has-treewidth-a.md)

## Sources

- M. Arenas, P. Barceló, L. Libkin, W. Martens and A. Pieris, *Database Theory: Querying Data*, preliminary version of 19 August 2022, open access at <https://github.com/pdm-book/community>, Theorem 23.2 and the outline of its proof (pp. 193–198).
- M. Grohe, "The complexity of homomorphism and constraint satisfaction problems seen from the other side", *Journal of the ACM* 54(1), Article 1, 2007, Theorem 1.1 and Corollary 6.3.
