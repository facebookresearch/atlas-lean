# Priority Queue

ADT `Priority_Queue` (book Fig. 14.1): interface, abstraction
function `mset`, invariant `invar`, and the seven specification
clauses (`empty`, `empty-inv`, `insert`, `insert-inv`, `del_min`,
`del_min-inv`, `get_min`).

Two renderings of Isabelle/HOL in the book are made explicit here:
* The book's `get_min : 0q → 0a` is partial (unspecified on the
  empty queue); here it is `Option`-valued, and the `del_min` /
  `get_min` clauses are stated for `mset q ≠ 0`, exactly as in the
  book, with the minimum produced as `some m`.
* The book writes the `del_min` clause as
  `mset (del_min q) = mset q - {#get_min q#}` (remove one occurrence
  of the minimum). It is stated here in the equivalent additive form
  `mset (del_min q) + {m} = mset q`, which is the form the
  skew-heap proof produces directly (`mset_delMin_add`) and which
  avoids committing to a particular multiset-difference operation.
