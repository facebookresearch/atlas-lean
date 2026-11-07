# Differences of fractional parts of multiples of the golden ratio

Let $F_m$ be the $m$-th
Fibonacci number, with $F_0 = 0$ and $F_1 = 1$, let $\varphi = (1 + \sqrt{5})/2$ be the golden
ratio, and write $\{y\} = y - \lfloor y \rfloor$ for the fractional part. Let $i \ge 1$ be a
natural number, put $g_i = F_{3i}/2$ (an integer, since $F_{3i}$ is even), and let
$x_1, x_2, m_1, m_2$ be integers. Then:
(i) if $g_i$ is even, $2(x_2 - x_1) = g_i$, $x_1 = \lfloor m_1\varphi \rfloor$ and
$x_2 = \lfloor m_2\varphi \rfloor$, then
$\{m_2\varphi\} - \{m_1\varphi\} \le (\varphi^{-3i+1} - \varphi)/4 < -0.38$;
(ii) if $g_i$ is odd, $2(x_2 - x_1) = g_i + 1$, $x_1 = \lfloor m_1\varphi \rfloor$ and
$x_2 + 1 = \lfloor m_2\varphi \rfloor$, then
$\{m_2\varphi\} - \{m_1\varphi\} < (3\varphi - 6)/4 < -0.28$;
(iii) if $g_i$ is odd, $i > 1$, $2(x_2 - x_1) = g_i - 1$, $x_1 + 1 = \lfloor m_1\varphi \rfloor$
and $x_2 = \lfloor m_2\varphi \rfloor$, then
$\{m_2\varphi\} - \{m_1\varphi\} < (-5\varphi + 6)/4 < -0.52$.

The paper states (i) with a strict inequality, but equality occurs: $i = 2$, $m_1 = 1$, $m_2 = 2$,
$x_1 = 1$, $x_2 = 3$ give $\{2\varphi\} - \{\varphi\} = (\varphi^{-5} - \varphi)/4$.

## Sources

- William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other Sequences*, INTEGERS 25 (2025), Article A29, Lemma 4 (`integers-2025-A29-lem-4`).
