# Powers of two when $P \equiv 2$ and $-Q \equiv 1 \pmod 4$

Let $P$ and $Q \ne 0$ be
integers forming a nondegenerate Lucas pair with $P \equiv 2 \pmod 4$ and $-Q \equiv 1 \pmod 4$,
and let $U$ be the Lucas sequence given by $U_0 = 0$, $U_1 = 1$ and
$U_{k+2} = P U_{k+1} - Q U_k$. Let $S(U)$ be the set of positive integers $n$ coprime to $Q$ such
that the period $\pi_U(n)$ of $U$ modulo $n$ divides $n$, let $S'(U)$ be the set of $n \in S(U)$
with $n \mid U_1 + \dots + U_n$, and say that a natural number $x$ has integral averages if
$x \mid w_1 + \dots + w_x$ for every integer sequence $(w_k)_{k \ge 0}$ with
$w_{k+2} = P w_{k+1} - Q w_k$ for all $k$. Then $2^i \in S(U)$ for every $i \ge 1$; for every
$k \ge 2$ and every natural number $n$ with $2^k \mid n$ and $2^{k+1} \nmid n$, one has
$2^k \mid U_1 + \dots + U_n$; the least even element of $S'(U)$ is $4$, while the least even
element of $S(U)$ is $2$; and for every $k \ge 2$, $2^k$ is the least multiple of $2^k$ in
$S'(U)$ and in $S(U)$, and $2^k$ has integral averages.

In the paper's notation $a = P$ and $b = -Q$, so the hypotheses are $a \equiv 2$ and
$b \equiv 1 \pmod 4$.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.15 (`integers-2024-A36-thm-2-15`).
