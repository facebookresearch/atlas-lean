# The coefficients give the tree length

Let $S$ be a finite set of clusters with $|S| \ge 3$, $a, b \in S$ distinct, $\ell$ real pendant lengths and $m$ real, and let $D$ satisfy, for distinct $u, v \in S$,

- $D(u, v) = \ell(u) + \ell(v)$ if both $u, v \in \{a, b\}$;
- $D(u, v) = \ell(u) + m + \ell(v)$ if exactly one of $u, v$ is in $\{a, b\}$;
- $D(u, v) = \ell(u) + \ell(v)$ if neither is.

Then the [cherry-tree length](cherry-length.md) satisfies $L_{ab} = \sum_{c \in S} \ell(c) + m$, the total edge length of $T_{ab}$.
