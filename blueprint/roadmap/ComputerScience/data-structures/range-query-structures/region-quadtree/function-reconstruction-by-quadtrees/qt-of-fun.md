# Full quadtree sampled from a function

Let $f$ map pairs of natural numbers to a type $A$. The quadtree of scale $n$ sampled from $f$ is
defined by recursion on $n$: at scale $0$ it is the leaf $L(f(0, 0))$; at scale $n + 1$ it is the
branch $Q(t_0, t_1, t_2, t_3)$ whose children are the quadtrees of scale $n$ sampled from the
functions $(i, j) \mapsto f(i, j)$, $(i, j) \mapsto f(i, j + 2^n)$, $(i, j) \mapsto f(i + 2^n, j)$
and $(i, j) \mapsto f(i + 2^n, j + 2^n)$ respectively. Equal leaves are not merged.
