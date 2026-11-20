# Metric of a dated rooted tree

A real function $d$ on pairs of taxa of a finite set $X$ is the metric of a dated rooted tree if there are a [hierarchy](is-hierarchy.md) $H$ on $X$ and dates $h$ on subsets of $X$ such that

- $h(\{x\}) = 0$ for every taxon $x$;
- $h(C) < h(D)$ whenever $C, D \in H$ and $C \subsetneq D$;
- for all $x, y$ there is $C \in H$ containing $x$ and $y$ with $d(x, y) = h(C)$ and $C \subseteq D$ for every $D \in H$ containing $x$ and $y$.

With edge lengths $(h(D) - h(C))/2$ from each cluster to its parent, $d(x, y)$ is the path length and all leaves are equidistant from the root (Semple & Steel 2003).

## Sources

- C. Semple and M. Steel, *Phylogenetics*, Oxford University Press (2003).
