# Repairs are block selections

Let $db$ be a finite instance over a schema with one primary key per relation, and call a set of facts consistent if no two distinct facts
in it agree on the relation name and the key. A block of $db$ is a maximal set of facts of $db$ of one relation that agree on its key. A subinstance $r \subseteq db$ is a maximal (under inclusion) consistent subset of $db$ if and only if
$r$ contains exactly one fact of every block of $db$.

## Proof

Facts in different blocks never conflict, and two facts in the same block always do. A consistent subset therefore contains at most one fact
per block; if it misses a block, adding any fact of that block keeps it consistent, so it is not maximal. Conversely, a subset with exactly one fact
per block is consistent, and adding any other fact of $db$ puts two facts in one block.

## Depends on

- [Repairs and consistent query answering under primary keys](repairs-and-consistent-query-answering-under-primary-keys.md)

## Sources

- P. Koutris and J. Wijsen, *A trichotomy in the data complexity of certain query answering for conjunctive queries*, arXiv:1501.07864v1, Section 3 (a block is a maximal set of key-equal facts; a repair is a maximal consistent subset). <https://arxiv.org/pdf/1501.07864v1>
