# Grouping and aggregation semantics

This node collects grouping and aggregation over finite bags and the rewrite that performs aggregation
before a join.

## Expansion

A sound expansion has separate pages for:

1. **Grouping.** $\gamma_{G;F}$ groups a finite bag by the attributes $G$ and applies $F$ to the nonempty bag of
   argument tuples of each existing group; there is no output row for an empty input.
2. **Partial aggregates.** COUNT, SUM, MIN and MAX decompose over a partition of a group; AVG is SUM divided by
   COUNT on nonempty groups.
3. **Aggregation before join.** Late and early aggregation give equal bags when (FD1) the final grouping
   attributes determine the left pre-aggregation key and (FD2) the left pre-aggregation key together with
   the right grouping attributes determine a single right tuple occurrence. In particular this holds when
   FD1 holds and the equijoin binds a full candidate key of the right relation; a foreign key is not
   needed for the equality. The rewrite applies to any aggregate function $F$ defined on bags whose
   arguments are attributes of the left relation, followed by a common final projection or duplicate
   elimination.
4. **Scope.** This finite-bag result does not claim the unqualified SQL forms of the cited source, which fail
   on an empty left input, nor a necessity theorem; SQL NULL handling and global aggregates on empty inputs
   are outside this node.

## Depends on

- [Bag relations and bag relational algebra](bag-relations-and-bag-relational-algebra.md)

## Sources

- Foundations of Databases (Abiteboul, Hull, Vianu) — Abiteboul, Hull, Vianu; authors' free web edition (webdam.inria.fr/Alice). <http://webdam.inria.fr/Alice/pdfs/all.pdf> Background reference.
- Performing Group-By before Join (Yan and Larson), manuscript copy, Section 4.3 (functional dependencies), Section 5, Theorem 1 and Theorem 2 (the aggregation columns belong to the first relation). <https://cs.uwaterloo.ca/~gweddell/cs848/YanLarson.pdf>
