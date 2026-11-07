# Sums of eight degenerate second-order recurrences

For an integer sequence
$(w_j)_{j \ge 0}$ write $B_w(n) = w_1 + \dots + w_n$. Let $u$ be the sequence with $u_0 = 0$,
$u_1 = 1$ and $u_{j+2} = u_j$, and $v$ the sequence with $v_0 = 0$, $v_1 = 1$ and
$v_{j+2} = -2 v_{j+1} - v_j$. For every $n \ge 1$: $B_u(n) = \lfloor (n + 1) / 2 \rfloor$ and
$B_v(n) = (-1)^{n+1} \lfloor (n + 1) / 2 \rfloor$; $n$ divides $B_w(n)$ for every integer
sequence $w$ with $w_{j+2} = w_j$ if and only if $n = 1$; $n$ divides $B_w(n)$ for every integer
sequence $w$ with $w_{j+2} = 2 w_{j+1} - w_j$ if and only if $n$ is odd; and $n$ divides
$B_w(n)$ for every integer sequence $w$ with $w_{j+2} = -2 w_{j+1} - w_j$ if and only if
$n = 1$. For every integer sequence $w$ and every $n \in \mathbb{N}$: if $w_{j+2} = -w_j$ for all
$j$, then $B_w(4n) = 0$; if $w_{j+2} = w_{j+1} - w_j$ for all $j$, then $B_w(6n) = 0$; if
$w_{j+2} = -w_{j+1} - w_j$ for all $j$, then $B_w(3n) = 0$; if $w_{j+2} = w_{j+1}$ for all $j$,
then $B_w(n) = n w_1$; if $w_{j+2} = -w_{j+1}$ for all $j$, then $B_w(2n) = 0$; and if
$w_{j+2} = 2 w_{j+1} - w_j$ for all $j$, then $2 B_w(n) = (w_1 - w_0) n (n + 1) + 2 w_0 n$ and,
when $n \ge 1$, $B_w(2n - 1) = (2n - 1)(n (w_1 - w_0) + w_0)$.

In the paper's notation $W_{j+2} = a W_{j+1} + b W_j$ these are the pairs $(a, b) = (0, 1)$,
$(0, -1)$, $(1, -1)$, $(-1, -1)$, $(2, -1)$, $(-2, -1)$, $(1, 0)$ and $(-1, 0)$.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.1 (`integers-2024-A36-thm-2-1`).
