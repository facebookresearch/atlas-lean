# Splitting off the first arc

Let $n = j + m + 2$. The noncrossing perfect matchings $f$ of $\{0, \dots, n-1\}$ with
$f(0) = j + 1$ are in bijection with pairs $(g, h)$ of noncrossing perfect matchings of
$\{0, \dots, j-1\}$ and of $\{0, \dots, m-1\}$:

- $g(i) = f(i + 1) - 1$ for $0 \le i < j$ and $g(i) = i$ for $i \ge j$: the matching of the $j$
  points $1, \dots, j$ strictly inside the arc $\{0, j+1\}$, shifted down by one;
- $h(i) = f(i + j + 2) - (j + 2)$ for $0 \le i < m$ and $h(i) = i$ for $i \ge m$: the matching of
  the $m$ points $j + 2, \dots, n - 1$ to the right of the arc, shifted down by $j + 2$.

The noncrossing condition is what makes this work: a point strictly inside the arc
$\{0, f(0)\}$ is matched inside it, and so a point to its right is matched to its right. The
inverse glues $g$ and $h$ back around the arc $\{0, j+1\}$.

## Background

- [Noncrossing perfect matching](is-ncmatching.md): the nested-arcs condition, applied to the arc
  $\{0, f(0)\}$.
