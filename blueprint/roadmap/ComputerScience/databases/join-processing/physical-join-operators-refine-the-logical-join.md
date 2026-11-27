# Physical join operators refine the logical join

This node collects the correctness contracts of the standard physical join algorithms over finite
relations. Nested-loop join tests every pair of tuples against the join condition, so it computes the
theta join $r \bowtie_\theta s$; block nested-loop join computes the same result for every partition
of the inputs into blocks. Merge join and hash join apply only to equi-joins and natural joins. Each
contract says that the algorithm's output equals the logical join: as a set under set semantics, and
under bag semantics (multiplicities in $\mathbb{N}$) with one output tuple for each pair of input occurrences
that satisfies the join condition, so that the multiplicity of an output tuple is the sum, over the pairs
of input tuples producing it, of the products of their multiplicities. Correctness and cost are separate
statements; costs are stated only relative to an explicit input/output model.

## Expansion

A sound expansion has separate pages for:

1. nested-loop and block nested-loop join compute the theta join, for any join condition;
2. merge join computes the equi-join when both inputs are sorted by the join attributes under a total
   order on join values, provided that every tuple of a group of equal join values in one input is
   matched with every tuple of the equal-valued group in the other (duplicate join values);
3. hash join computes the equi-join for every partitioning function $h$ on join values: tuples with
   equal join values fall in partitions with the same index, so joining each pair of partitions
   $r_i$, $s_i$ and keeping only pairs whose join values are equal gives exactly the equi-join;
   unequal values with equal $h$ (collisions) only produce candidate pairs that the equality test
   rejects;
4. block-transfer and seek cost estimates stated in the shared external-memory model with access paths, using its
   external merge-sort cost for merge join, as statements separate from correctness.

## Depends on

- [Relational algebra queries](../relational-algebra/expr.md)
- [Bag relations and bag relational algebra](../bags-and-nulls/bag-relations-and-bag-relational-algebra.md)

## Sources

- A. Silberschatz, H. F. Korth and S. Sudarshan, *Database System Concepts*, 7th edition, Chapter 15
  slides (query processing): nested-loop join, block nested-loop join, merge-join (equi-joins and
  natural joins, sorting on the join attribute, matching every pair with the same join value) and
  hash-join (partitioning by $h$ on the join attributes; matching tuples located within partition
  $s_i$). <https://www.db-book.com/slides-dir/PDF-dir/ch15.pdf>
