# P-positions of the gold game

Let $\varphi$ be the golden ratio and $F_n$ the Fibonacci
numbers ($F_1 = F_2 = 1$). In the gold game a heap of $n$ tokens may be removed entirely when
$n = \lfloor k\varphi \rfloor$ for some integer $k \ge 1$, and $i$ tokens may be removed from a
heap of $n > i$ tokens, leaving $n - i$, when $i = \lfloor k(1 + \varphi) \rfloor$ for some
integer $k \ge 1$ (the Beatty octal moves for $\varphi$ and $1 + \varphi$). Let $S$ be the set of
natural numbers consisting of $0$ and the $F_{2k+1}$ for $k \ge 1$, that is $0, 2, 5, 13, 34, \dots$
Then $S$ is stable: no move leads from a heap size in $S$ to a heap size in $S$. And $S$ is
absorbing: from every heap size outside $S$ some move leads to a heap size in $S$.

Since every move shrinks the heap, a stable and absorbing set is the set of P-positions, so the
P-positions of the gold game are exactly the heap sizes in $S$.

## Sources

- Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 3.
