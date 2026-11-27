# Arborally satisfied supersets are realized by offline BST executions

For every arborally satisfied superset $Y$ of an access sequence $X$, there is an offline BST execution on $X$, starting from a suitable initial tree, that touches exactly the keys $\{a : (a, t) \in Y\}$ at each time $t$; its cost in the touched-node model is $|Y|$.

## Proof sketch

Let $N(a, t)$ be the smallest time $s \ge t$ with $(a, s) \in Y$ (or $\infty$), and let $T_t$ be a treap on the keys with priority $N(a, t)$, earlier times nearer the root. The keys of row $t$ of $Y$ have the minimum possible priority value $t$, so by the treap property they form a connected subtree of $T_t$ containing the root, and the execution rearranges exactly this subtree into treap order for the priorities $N(\cdot, t+1)$. The result is $T_{t+1}$: the heap property can fail only between a touched parent $q$ and an untouched child $r$, and then the rectangle spanned by $(q, t)$ and $(r, N(r, t))$ would have no point of $Y$ on its sides incident to $(q,t)$, contradicting arboral satisfaction.

## Depends on

- [Arborally satisfied point sets](arborally-satisfied-set.md)
- [Point set of an access sequence and touched set of a BST execution](access-point-set.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
