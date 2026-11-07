# End blocks ending in $1$ are Lucas–Wythoff sequences

Let $\varphi$ be the golden ratio
and $L_n$ the Lucas numbers. For integers $p, q, r$ let $V(p, q, r)$ be the set of the integers
$p \lfloor n\varphi \rfloor + qn + r$ with $n \ge 1$, and $V_0(p, q, r)$ the same set with
$n \ge 0$. For a word $w = w_{m-1} \cdots w_0$ of length $m$ over the natural numbers, let $R_w$ be
the set of natural numbers $N$ with a base phi expansion whose digit at position $i$ is $1$
exactly when $w_i = 1$, for $i = m - 1, \dots, 0$. Then:
(1) for every word $w = w_{m-1} \cdots w_0$ of length $m \ge 3$ with letters in $\{0, 1\}$, no two
consecutive letters $1$ and $w_0 = 1$, which is not of the form $0^k 1$ or $1 0^k 1$ with
$k \ge 2$, and for which $R_w$ is nonempty, there is an integer $\gamma \le 0$ such that every
natural number $N \ge 1$ lies in $R_w$ if and only if it lies in $V(L_{m-2}, L_{m-3}, \gamma)$
when $w_{m-1} = 0$, respectively in $V(L_{m-1}, L_{m-2}, \gamma)$ when $w_{m-1} = 1$;
(2) for every $m \ge 1$ and every natural number $N \ge 1$: $N \in R_{0^{2m} 1}$ if and only if
$N \in V_0(L_{2m+1}, L_{2m}, 1)$; $N \in R_{0^{2m+1} 1}$ if and only if
$N \in V_0(L_{2m+1}, L_{2m}, 1)$; $N \notin R_{1 0^{2m} 1}$; and $N \in R_{1 0^{2m+1} 1}$ if and
only if $N \in V(L_{2m+2}, L_{2m+1}, 1 - L_{2m+1})$.

The hypothesis that $R_w$ is nonempty is added to the printed statement: as printed, the
statement fails for $w = 01001$, which never occurs (its end block $1001$ is excluded), while
every $V(p, q, \gamma)$ is nonempty; the source's proof derives its description of $R_w$ only
under the assumption $R_w \ne \emptyset$.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Theorem 8 (`integers-2024-A24-thm-8`).
