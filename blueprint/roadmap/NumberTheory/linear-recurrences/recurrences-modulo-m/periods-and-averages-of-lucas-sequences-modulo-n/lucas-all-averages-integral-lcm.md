# Integral averages extend to least common multiples

Let $U$ be the Lucas sequence with
parameters $P$ and $Q \ne 0$, given by $U_0 = 0$, $U_1 = 1$ and $U_{k+2} = P U_{k+1} - Q U_k$, and
let $S'(U)$ be the set of positive integers $n$ coprime to $Q$ such that the period $\pi_U(n)$ of
$U$ modulo $n$ divides $n$ and $n \mid U_1 + \dots + U_n$. Call an integer sequence
$(w_k)_{k \ge 0}$ a recurrence if $w_{k+2} = P w_{k+1} - Q w_k$ for all $k$, and say that a
natural number $x$ has integral averages if $x \mid w_1 + \dots + w_x$ for every recurrence $w$.
Let $n > 0$ be such that every recurrence $w$ satisfies $w_{k+n} \equiv w_k \pmod n$ for all
$k \ge 1$, and suppose $n$ has integral averages. Then $\operatorname{lcm}(m, n)$ has integral
averages for every $m \in S'(U)$.

In the paper's notation $a = P$ and $b = -Q$, and the recurrences are the sequences $W(a, b)$.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.7.
