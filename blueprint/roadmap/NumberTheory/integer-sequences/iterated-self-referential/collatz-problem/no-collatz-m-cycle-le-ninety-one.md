# No Collatz $m$-cycles with $m \le 91$ (Hercher)

Let $T$ be the shortcut Collatz map on
the natural numbers, $T(c) = c/2$ for even $c$ and $T(c) = (3c+1)/2$ for odd $c$, and let $m$ be
a natural number with $m \le 91$. There are no natural numbers $n$ and $p > 0$ such that
$T^i(n) > 2$ for all $i < p$, $T^p(n) = n$, $T^k(n) \ne n$ for all $k$ with $0 < k < p$, and
exactly $m$ indices $i < p$ satisfy both $T^i(n) < T^{(i+1) \bmod p}(n)$ and
$T^i(n) < T^{(i+p-1) \bmod p}(n)$.

In words: no cycle of $T$ all of whose entries exceed $2$ (which excludes the trivial cycle
$1, 2, 1, 2, \dots$), taken with its minimal period $p$, has exactly $m$ entries lying cyclically
strictly below both neighbours.

## Sources

- Christian Hercher, *There are no Collatz $m$-Cycles with $m \le 91$*, Journal of Integer Sequences 26 (2023), Article 23.3.5, Theorem 23 (Main Theorem), with the map in Definition 1 and $m$-cycles in Definition 5, https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.tex.
