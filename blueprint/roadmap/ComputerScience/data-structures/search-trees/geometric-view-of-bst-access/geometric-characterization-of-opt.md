# Geometric characterization of the optimal offline BST cost

For every access sequence $X$, the optimal offline BST cost satisfies $\mathrm{OPT}(X) = \Theta\big(\min\{|Y| : Y \text{ is an arborally satisfied superset of } X\}\big)$; that is, offline binary search tree optimization is equivalent, up to a constant factor, to the purely combinatorial problem of finding a smallest arborally satisfied superset of $P(X)$.

## Proof sketch

The touched set of an optimal execution is an arborally satisfied superset by the first lemma, giving $\min |Y| \le \mathrm{OPT}(X)$. Conversely, a minimum superset is realized by an execution of cost $|Y|$ by the second lemma, and the rotations of the treap rearrangement cost $O(|Y|)$.

## Depends on

- [Arborally satisfied point sets](arborally-satisfied-set.md)
- [Point set of an access sequence and touched set of a BST execution](access-point-set.md)
- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Proof depends on

- [Touched sets of BST executions are arborally satisfied](touched-sets-are-arborally-satisfied.md)
- [Arborally satisfied supersets are realized by offline BST executions](arborally-satisfied-sets-are-executions.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
