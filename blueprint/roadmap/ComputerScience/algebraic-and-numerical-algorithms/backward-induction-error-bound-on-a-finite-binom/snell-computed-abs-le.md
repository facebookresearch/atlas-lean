# Snell computed abs le

Let $0 \le p \le 1$, $\mathrm{disc} > 0$ and $\varepsilon \ge 0$, and let $V(k, s)$ be a computed recursion over the number $k$ of steps and the path $s$, with exact terminal values $V(0, \cdot) = g$, such that at every $k$ and $s$
$$\bigl| V(k+1, s) - \max\bigl(g(s),\ \mathrm{disc} \cdot [\,p\, V(k, \mathrm{true} :: s) + (1 - p)\, V(k, \mathrm{false} :: s)\,]\bigr) \bigr| \le \varepsilon,$$
the children being the computed values at step $k$, not exact envelope values. Then after $N$ steps, $|\mathrm{snell}(N, s) - V(N, s)| \le \varepsilon \sum_{j < N} \mathrm{disc}^j$ at every node, in particular at the root.
