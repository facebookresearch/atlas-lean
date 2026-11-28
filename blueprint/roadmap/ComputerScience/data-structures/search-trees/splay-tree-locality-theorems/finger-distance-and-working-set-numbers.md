# Finger distance and working-set numbers of an access sequence

Let $s$ be a finite set of keys in a splay tree and $x_1, \dots, x_m$ a sequence of accesses to keys of $s$.

- For a fixed *finger* $f \in s$, the *finger distance* $d(f, y)$ is the number of keys of $s$ strictly between $f$ and $y$ plus one for $y \ne f$ (and $0$ for $y = f$); for $s = \{1, \dots, n\}$ it is $|y - f|$.
- The *working-set number* $t(j)$ of access $j$ is the number of distinct keys accessed since the previous access to $x_j$ (or since the start, if $x_j$ was not accessed before), including $x_j$ itself.

## Depends on

- [Splay operation](../splay-tree/splay.md)

## Sources

- D. D. Sleator and R. E. Tarjan, "Self-Adjusting Binary Search Trees", Journal of the ACM 32(3), 1985.
