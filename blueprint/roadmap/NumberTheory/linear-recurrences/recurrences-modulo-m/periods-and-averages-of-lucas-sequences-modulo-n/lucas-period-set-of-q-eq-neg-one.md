# Least period and average multiples for $Q = -1$

Let $U$ be the Lucas sequence
$U_0 = 0$, $U_1 = 1$, $U_{j+2} = P U_{j+1} - Q U_j$ with $Q = -1$ and $(P, Q)$ nondegenerate.
Write $\pi(m)$ for the period of $U$ modulo $m$ and $\pi^i$ for the $i$-th iterate of $\pi$
($\pi^0(m) = m$). Let $S$ be the set of positive integers $m$ coprime to $Q$ with
$\pi(m) \mid m$, and $S'$ the set of $m \in S$ with $m \mid U_1 + \cdots + U_m$. Say the orbit
of $n$ closes at $k$ if $\pi^i(n)$ is coprime to $Q$ for all $i \le k$ and
$\pi^{k+1}(n) = \pi^j(n)$ for some $j \le k$; let $\omega(n)$ be the least such $k$ ($0$ if
there is none) and $L(n) = \operatorname{lcm}(\pi^0(n), \pi^1(n), \dots, \pi^{\omega(n)}(n))$.
Call $m$ *integral for all recurrences* if every integer sequence $w$ with
$w_{j+2} = P w_{j+1} - Q w_j$ for all $j \ge 0$ satisfies $m \mid w_1 + \cdots + w_m$. Then:

(i) for every $n \ge 1$ the orbit of $n$ closes at some $k$, and $L(n)$ is the least element of
$S$ divisible by $n$; for every $n > 1$, $L(n)$ is even and $L(2) \mid L(n)$; $\pi(n)$ is even
for every $n \ge 3$; and $\pi(2)$ is even if $P$ is even;

(ii) if $P$ is odd, then for every $n \ge 1$ the least element of $S'$ divisible by $n$ is
$L(n)$, and $L(n)$ is integral for all recurrences; moreover $L(2) = 24$ if
$P \equiv \pm 1 \pmod 6$, and $L(2) = 6$ if $P \equiv 3 \pmod 6$;

(iii) if $P \equiv 2 \pmod 4$, then $L(2) = 2$, and for every $n \ge 1$: if
$L(n) \not\equiv 2 \pmod 4$, the least element of $S'$ divisible by $n$ is $L(n)$ and $L(n)$ is
integral for all recurrences; if $L(n) \equiv 2 \pmod 4$, the least element of $S'$ divisible
by $n$ is $2L(n)$ and $2L(n)$ is integral for all recurrences;

(iv) if $P \equiv 0 \pmod 4$, then for every $n \ge 2$, $n \notin S'$ and no element of $S'$ is
divisible by $n$; $n \nmid U_1 + \cdots + U_n$ for every even $n \ge 1$; and every $n \ge 1$
with $n \mid U_1 + \cdots + U_n$ is odd.

The case split in (iii) is on $L(n)$ modulo $4$, not on $n$ modulo $4$: for $P = 6$ and $n = 3$
the least element of $S$ divisible by $3$ is $6$, while the least element of $S'$ divisible by
$3$ is $12$.

## Sources

- Michal Křížek and Lawrence Somer, *Period Lengths Modulo n and Average of Terms of Second Order Linear Recurrences*, INTEGERS 24 (2024), Article A36, Theorem 2.24 (`integers-2024-A36-thm-2-24`).
