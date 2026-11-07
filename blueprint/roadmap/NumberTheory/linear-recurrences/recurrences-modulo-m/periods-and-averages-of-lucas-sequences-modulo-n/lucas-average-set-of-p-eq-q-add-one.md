# Period and average sets when $P = Q + 1$

Let $P$ and $Q \ne 0$ be integers forming a
nondegenerate Lucas pair with $P = Q + 1$, so that the roots of $x^2 - Px + Q$ are $Q$ and $1$,
and let $U$ be the Lucas sequence given by $U_0 = 0$, $U_1 = 1$ and
$U_{k+2} = P U_{k+1} - Q U_k$. Write $\pi_U(n)$ for the period of $U$ modulo $n$, $\rho_U(n)$ for
the least $s > 0$ with $n \mid U_s$ and $U_{s+1}$ coprime to $n$, $S(U)$ for the set of positive
integers $n$ coprime to $Q$ with $\pi_U(n) \mid n$, $S'(U)$ for the set of $n \in S(U)$ with
$n \mid U_1 + \dots + U_n$, and $T(U)$ for the set of positive integers $n$ coprime to $Q$ with
$n \mid U_n$. Say that a natural number $x$ has integral averages if $x \mid w_1 + \dots + w_x$
for every integer sequence $(w_k)_{k \ge 0}$ with $w_{k+2} = P w_{k+1} - Q w_k$ for all $k$.
Then $\pi_U(n) = \rho_U(n)$ for every $n > 0$ coprime to $Q$; $mn$ has integral averages for all
$n > 0$ dividing $Q$ and all $m \in S'(U)$; and $S(U) = T(U)$. If $P$ is odd, then
$S'(U) = S(U)$, every $n \in S(U)$ and every $n > 0$ dividing $Q$ has integral averages, and if
moreover $P = 3$, then $P^2 - 4Q = 1$ and $S(U) = \{1\}$. If $P$ is even, then $S'(U)$ consists
of the odd elements of $S(U)$, every odd $n \in S(U)$ has integral averages, and if
$P = 2 + 2^k$ for some $k \ge 1$, then no $n > 1$ lies in $S'(U)$.

In the paper's notation $a = P$ and $b = -Q$, so the hypothesis is $b = -a + 1$, and the paper's
$E_U(n) = 1$ is $\pi_U(n) = \rho_U(n)$; the paper's conditions $a \ne 0, 1, 2$ follow from
nondegeneracy. The paper's condition on even $a$ is read as $a = 2 + 2^k$ (the exponent is set as
a superscript); the linear reading $a = 2 + 2k$ is false: for $a = 8$ ($b = -7$) one has
$\pi_U(3) = 3$ and $3 \mid U_1 + U_2 + U_3 = 1 + 8 + 57 = 66$, so $3 \in S'(U)$.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.26 (`integers-2024-A36-thm-2-26`).
