# End blocks ending in $0$ are Lucas–Wythoff sequences

Let $\varphi$ be the golden ratio
and $L_n$ the Lucas numbers. For integers $p, q, r$ let $V(p, q, r)$ be the set of the integers
$p \lfloor n\varphi \rfloor + qn + r$ with $n \ge 1$, and $V_0(p, q, r)$ the same set with
$n \ge 0$. For a word $w = w_{m-1} \cdots w_0$ of length $m$ over the natural numbers, let $R_w$ be
the set of natural numbers $N$ with a base phi expansion whose digit at position $i$ is $1$
exactly when $w_i = 1$, for $i = m - 1, \dots, 0$. Then:
(1) for every word $w = w_{m-1} \cdots w_0$ of length $m \ge 2$ with letters in $\{0, 1\}$, no two
consecutive letters $1$, $w_0 = 0$ and $w \ne 0^m$, there is an integer $\gamma \le 0$ such that
every natural number $N \ge 1$ lies in $R_w$ if and only if it lies in
$V(L_{m-2}, L_{m-3}, \gamma)$ when $w_{m-1} = 0$, respectively in $V(L_{m-1}, L_{m-2}, \gamma)$
when $w_{m-1} = 1$;
(2) for every $m \ge 1$ and every natural number $N \ge 1$, $N \in R_{0^{2m}}$ if and only if
$N \in V(L_{2m}, L_{2m-1}, 1) \cup V_0(L_{2m-1}, L_{2m-2}, 0)$, and $N \in R_{0^{2m+1}}$ if and
only if $N \in V_0(L_{2m+1}, L_{2m}, 0) \cup V(L_{2m}, L_{2m-1}, 1)$; moreover
$V(L_{2m}, L_{2m-1}, 1)$ and $V_0(L_{2m-1}, L_{2m-2}, 0)$ are disjoint, and
$V_0(L_{2m+1}, L_{2m}, 0)$ and $V(L_{2m}, L_{2m-1}, 1)$ are disjoint.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Theorem 7.
