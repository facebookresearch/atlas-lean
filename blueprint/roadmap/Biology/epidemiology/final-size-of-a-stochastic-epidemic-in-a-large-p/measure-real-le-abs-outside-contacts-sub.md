# Chebyshev bound for the number of contacts outside $S_0$

Let the offspring numbers $\xi_{n,i}$ and the contact targets $U_j$ form a
[final-size epidemic model](is-final-size-epidemic.md) on a probability space $(\Omega, P)$, in the
population $\{0, \dots, N-1\}$, with offspring law $\nu$, a probability measure on $\mathbb{N}$. For
every set $S_0$ of $\#S_0$ initially susceptible individuals, every $m \in \mathbb{N}$ and every
real $t > 0$,
$P\Bigl(\Bigl|O_m - m \, \frac{N - \#S_0}{N}\Bigr| \ge t\Bigr) \le \frac{m \,(N - \#S_0)}{N t^2}$,
where $O_m$ is the [number of the first $m$ contacts outside $S_0$](outside-contacts.md) for the
targets $U_j(\omega)$.
