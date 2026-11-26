# Arborally satisfied supersets are realized by offline BST executions

For every arborally satisfied superset $Y$ of an access sequence $X$, there is an offline BST algorithm whose execution on $X$, starting from a suitable initial tree, touches exactly the keys $\{a : (a, t) \in Y\}$ at each time $t$; its cost is $|Y|$.

## Proof sketch

At time $t$, maintain the tree as a treap keyed by the keys with priority equal to the next time at which each key appears in $Y$ (earlier means higher). The keys of row $t$ of $Y$ have the highest priority and, by arborally satisfaction, form a connected subtree containing the root; rearranging that subtree into the treap order for the updated priorities is a legal BST operation on the touched nodes only.

## Depends on

- [Touched sets of BST executions are arborally satisfied](touched-sets-are-arborally-satisfied.md)

## Proof depends on

- [Touched sets of BST executions are arborally satisfied](touched-sets-are-arborally-satisfied.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
