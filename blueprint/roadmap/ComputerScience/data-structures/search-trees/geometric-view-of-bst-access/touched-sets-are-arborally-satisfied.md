# Touched sets of BST executions are arborally satisfied

For every BST algorithm and every access sequence $X$, the touched set of its execution on $X$ is an arborally satisfied superset of $X$.

## Proof sketch

The touched set contains $P(X)$ because each access touches its key. Take touched points $(a, s)$ and $(b, t)$ with $a \ne b$ and $s < t$, and suppose for contradiction that the closed rectangle they span contains no other touched point. Let $c$ be the lowest common ancestor of $a$ and $b$ in the tree at time $s$; its key lies between $a$ and $b$, possibly equal to $b$. If $c \ne a$, then $c$ is touched at time $s$ on the way to $a$, so $(c, s)$ is another touched point in the rectangle. If $c = a$, then $a$ is an ancestor of $b$ at time $s$. By assumption $a$ is not touched at any time in $(s, t]$; since every rearranged subtree contains the root, the subtree of $a$, which contains $b$, is never rearranged before time $t$, so $a$ is still an ancestor of $b$ at time $t$ and is touched on the way to $b$, again a contradiction.

## Depends on

- [Arborally satisfied point sets](arborally-satisfied-set.md)
- [Point set of an access sequence and touched set of a BST execution](access-point-set.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
