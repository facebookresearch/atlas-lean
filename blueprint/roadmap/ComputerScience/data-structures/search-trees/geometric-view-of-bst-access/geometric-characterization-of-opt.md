# Geometric characterization of the optimal offline BST cost

For every access sequence $X$, the optimal offline BST cost, with the offline algorithm free to choose its initial tree, satisfies $\mathrm{OPT}(X) = \Theta\big(\min\{|Y| : Y \text{ is an arborally satisfied superset of } X\}\big)$; in the touched-node cost model the two sides are equal. Thus offline binary search tree optimization is equivalent, up to a constant factor, to the purely combinatorial problem of finding a smallest arborally satisfied superset of $P(X)$.

## Proof sketch

The touched set of any execution on $X$, an optimal one in particular, is an arborally satisfied superset of $X$ whose size is at most the cost of the execution, which gives $\min |Y| \le \mathrm{OPT}(X)$. Conversely, a minimum superset $Y$ is the touched set of an offline execution that touches $|Y|$ nodes in total; rearranging a touched subtree of $k$ nodes takes $O(k)$ rotations and pointer moves, so this execution costs $O(|Y|)$ in the pointer-and-rotation model.

## Depends on

- [Arborally satisfied point sets](arborally-satisfied-set.md)
- [Point set of an access sequence and touched set of a BST execution](access-point-set.md)
- [The binary search tree access model](../dynamic-optimality/the-binary-search-tree-access-model.md)

## Proof depends on

- [Touched sets of BST executions are arborally satisfied](touched-sets-are-arborally-satisfied.md)
- [Arborally satisfied supersets are realized by offline BST executions](arborally-satisfied-sets-are-executions.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
