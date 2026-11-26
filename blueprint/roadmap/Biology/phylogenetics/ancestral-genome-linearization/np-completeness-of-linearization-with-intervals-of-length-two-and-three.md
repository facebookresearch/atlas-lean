# NP-completeness of linearization with intervals of length two and three

**Setting.** As in
[linearization of ancestral adjacencies as a maximum weight 2m-matching](linearization-of-ancestral-adjacencies-as-a-maximum-weight-2m-matching.md),
ancestral gene intervals are rows of a binary matrix whose columns are genes; the **degree** of a row
is its number of 1 entries. A matrix is **component-Ci1P** (all multiplicities equal to one) if its
columns can be partitioned so that every row has its 1 entries in a single part and each part admits
a circular order in which every row's 1 entries are consecutive. MAX-ROW-component-Ci1P asks for a
maximum-weight subset of rows with this property.

**Theorem.** MAX-ROW-component-Ci1P is NP-complete for matrices whose rows have degree 2 or 3, even
when every row has weight one and every column multiplicity is one. Consequently it remains
NP-complete with weights and multiplicities.

**Intermediate results.**

1. 3SAT(2,3) is NP-complete: CNF satisfiability where every clause has two or three literals, every
   variable occurs exactly twice positively and once negatively, and exactly one positive occurrence
   lies in a 3-clause while the other two occurrences lie in 2-clauses.
2. Covering a 2,3-uniform hypergraph (hyperedges of two or three vertices) by vertex-disjoint cycles
   and paths after removing at most $k$ hyperedges (the 23UCR problem) is NP-complete.
3. A 2,3-uniform hypergraph $H$ has such a covering after removing at most $k$ hyperedges if and only
   if its incidence matrix $B_H$ is component-Ci1P after removing at most $k$ rows.

## Depends on

- [Linearization of ancestral adjacencies as a maximum weight 2m-matching](linearization-of-ancestral-adjacencies-as-a-maximum-weight-2m-matching.md)

## Expansion

Variable gadgets are hypergraph cycles in which exactly one of two main hyperedges must be removed,
encoding a truth value; implication cycles of 2-clauses force all copies of a variable to agree, and
3-clause gadgets can be covered only if some literal is true. Local exchange arguments show any valid
covering can be normalized to this "expected behavior", so satisfying assignments and coverings of the
constructed hypergraph correspond. Rows of degree 3 are what breaks the matching structure: unlike
adjacencies, a length-3 interval constrains the order of three genes at once, and the polynomial
degree-2 algorithm does not extend.

## Sources

- J. Maňuch, M. Patterson, R. Wittler, C. Chauve, E. Tannier, "Linearization of ancestral
  multichromosomal genomes", BMC Bioinformatics 13(Suppl 19) (2012) S11, Theorems 1-3 and Lemma 3,
  <https://doi.org/10.1186/1471-2105-13-s19-s11> (PMC3526452).
