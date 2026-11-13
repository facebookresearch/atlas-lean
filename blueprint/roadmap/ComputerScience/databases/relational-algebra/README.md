# Relational algebra

- [Tuple](tuple.md)
- [Tuple over a schema](is-over.md)
- [Compatible tuples](compatible.md)
- [Merge of two tuples](merge.md)
- [Compatibility with a merge, grouped from the left](compatible-merge-left.md)
- [Compatibility with a merge, grouped from the right](compatible-merge-right.md)
- [Restriction of a tuple](restrict.md)

## Selection conditions

- [Selection conditions](cond.md)
- [Truth value of a selection condition](eval.md)
- [Attributes of a selection condition](attrs.md)
- [Selection conditions depend only on their attributes](eval-restrict.md)

## The operators

- [Relation over a schema](is-over-2.md)
- [Selection](select.md)
- [Cascade of selections](select-select.md)
- [Selections commute](select-comm.md)
- [Natural join](join.md)
- [Renaming of attributes](rename.md)
- [Commutativity of the natural join](join-comm.md)
- [Associativity of the natural join](join-assoc.md)
- [The natural join on a common schema is the intersection](join-eq-inter.md)
- [Selection distributes over union](select-union.md)
- [Selection distributes over difference](select-sdiff.md)
- [Projection of a relation](project.md)
- [Membership in a join](mem-join-iff.md)
- [Selection pushdown into the left operand of a join](select-join-left.md)
- [Selection pushdown into the right operand of a join](select-join-right.md)
- [Cascade of projections](project-project.md)
- [Cascade of projections onto a subset](project-project-of-subset.md)
- [Selection commutes with projection](select-project.md)
- [Projection distributes over union](project-union.md)

## Queries

- [Relational algebra queries](expr.md)
- [Value of a query](eval-2.md)
- [Schema of a query](schema.md)
- [Databases conforming to a schema](conforms.md)
- [Typing is sound](eval-is-over.md)
- [Query equivalence](equiv.md)
- [Selection pushdown as a query rewrite](select-join.md)
- [Cascade of selections as a query rewrite](select-select-2.md)
- [Cascade of projections as a query rewrite](project-project-2.md)
