# Chebyshev bound for the number of hits among the first c contacts

Let the offspring numbers $\xi_{n,i}$ and the contact targets $U_j$ form a
[final-size epidemic model](is-final-size-epidemic.md) on a probability space $(\Omega, P)$, in the
population $\{0, \dots, N-1\}$, with offspring law $\nu$, a probability measure on $\mathbb{N}$. For
every set $S_0$ of $\#S_0$ initially susceptible individuals, every $c \in \mathbb{N}$ and every
real $t > 0$, $P(|H_c - \#S_0 (1 - ((N-1)/N)^c)| \ge t) \le \#S_0 / t^2$, where $H_c$ is the
[number of hits](hits.md) among the first $c$ contacts of the targets $U_j(\omega)$. Here
$\#S_0 (1 - (1 - 1/N)^c)$ is the mean of $H_c$: each individual of $S_0$ is missed by all of the
first $c$ contacts with probability $(1 - 1/N)^c$.
