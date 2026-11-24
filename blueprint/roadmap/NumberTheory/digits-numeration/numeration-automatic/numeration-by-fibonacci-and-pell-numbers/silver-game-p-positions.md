# P-positions of the silver game

Let $P_n$ be the Pell numbers and $H_n$ the Pell–Lucas
numbers ($H_0 = H_1 = 1$, $H_{n+2} = 2H_{n+1} + H_n$). In the silver game a heap of $n$ tokens
may be removed entirely when $n = \lfloor k(1 + \sqrt 2) \rfloor$ for some integer $k \ge 1$, and
$i$ tokens may be removed from a heap of $n > i$ tokens, leaving $n - i$, when
$i = \lfloor k(2 + \sqrt 2)/2 \rfloor$ for some integer $k \ge 1$ (the Beatty octal moves for
$1 + \sqrt 2$ and $(2 + \sqrt 2)/2$). Let $S$ be the set of natural numbers consisting of $0$ and
the $P_{2k+1}$ and $H_{2k+2}$ for $k \ge 0$, that is $0, 1, 3, 5, 17, 29, 99, \dots$ Then $S$ is
stable: no move leads from a heap size in $S$ to a heap size in $S$. And $S$ is absorbing: from
every heap size outside $S$ some move leads to a heap size in $S$.

Since every move shrinks the heap, a stable and absorbing set is the set of P-positions, so the
P-positions of the silver game are exactly the heap sizes in $S$.

## Sources

- Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 7.
