# Touched sets of BST executions are arborally satisfied

For every BST algorithm and every access sequence $X$, the touched set of its execution on $X$ is an arborally satisfied superset of $X$.

## Proof sketch

Take touched points $(a, s)$ and $(b, t)$ with $a < b$ and $s < t$. If no key in $[a, b]$ is touched at a time in $(s, t]$ other than $b$ at time $t$, then the lowest common ancestor of $a$ and $b$ after time $s$ is some key $c \in [a, b]$, and touching $b$ at time $t$ requires touching $c$ because the touched subtree contains the root. Either $c$ gives the required third point at time $t$, or $c = a$ and $(a,t)$ is touched, which is again inside the rectangle; the case $s = t$ does not arise because the points differ in both coordinates.

## Depends on

- [Arborally satisfied point sets](arborally-satisfied-set.md)
- [Point set of an access sequence and touched set of a BST execution](access-point-set.md)

## Sources

- Erik D. Demaine, Dion Harmon, John Iacono, Daniel Kane, Mihai Pătraşcu, "The Geometry of Binary Search Trees", SODA (2009).
