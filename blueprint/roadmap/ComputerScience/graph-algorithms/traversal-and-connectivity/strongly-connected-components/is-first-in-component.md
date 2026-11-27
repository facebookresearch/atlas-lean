# First vertex of a strongly connected component

A vertex $v$ is first in its strongly connected component when
$\mathrm{num}(v) \le \mathrm{num}(w)$ for every $w$
strongly connected to $v$: $v$ is the first vertex of its component reached by the search. By
[Corollary 11](tree-ancestor-of-first.md) it is the root of the subtree that the component forms
in the depth-first spanning forest, which Tarjan calls the root of the component.

## Sources

- R. E. Tarjan, *Depth-first search and linear graph algorithms*, SIAM J. Comput. 1(2) (1972)
  146–160, §4, Corollary 11.
