# The path metric on a partition into sides

Let $(G, \iota)$ be a [binary phylogenetic tree](is-binary-phylogenetic-tree.md) on a finite set $X$ with edge lengths $w_e > 0$ and path metric $d$, and let $S$ be a partition of $X$ into [sides of edges](side.md) (pairwise disjoint, covering $X$, each the side of some edge). Then there are a finite family $(A_e)_{e \in E}$ of subsets of $S$, weights $w'_e$ and reals $\rho(s, x)$ such that

- $w'_e > 0$ and $A_e \ne \emptyset$ for every $e$;
- the family is closed under complement in $S$, pairwise compatible, binary (every member with at least two elements is the disjoint union of two members) and contains every singleton $\{s\}$;
- if $|A_e| \ge 2$ and $|S \setminus A_e| \ge 2$, then $w'_e = w(uv)$ for some edge $uv$ with neither endpoint a taxon vertex;
- if $A_e = \{s, t\}$, then $s \cup t$ is the side of some edge;
- for distinct $s, t \in S$, $x \in s$ and $y \in t$:

$$d(x, y) = \frac12 \sum_{e \,:\, A_e \text{ separates } s, t} w'_e + \rho(s, x) + \rho(t, y).$$
