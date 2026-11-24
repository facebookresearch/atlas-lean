# Shor's order-to-factor reduction, existential form

Let $N$, $a$ and $r$ be natural
numbers with $N > 1$ and $a \ge 1$. If $a^r \equiv 1 \pmod{N}$, $r$ is even,
$a^{r/2} \not\equiv 1 \pmod{N}$ and $a^{r/2} \not\equiv -1 \pmod{N}$, then $N$ has a nontrivial
factor: there is a natural number $d$ with $d \mid N$ and $1 < d < N$.

One such factor is $\gcd(a^{r/2} - 1, N)$.
