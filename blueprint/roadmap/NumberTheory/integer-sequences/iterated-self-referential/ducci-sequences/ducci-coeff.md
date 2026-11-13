# Ducci coefficients

For natural numbers $n$, $r$ and $s$, the Ducci coefficient is
$a_{r,s} = \sum_{0 \le j \le r,\ j \equiv s - 1 \ (\mathrm{mod}\ n)} \binom{r}{j}$, where $s - 1$
is read as $0$ when $s = 0$ and congruence modulo $0$ is equality.

For $1 \le s \le n$, $a_{r,s}$ is the coefficient of $x_s$ in the first entry of $D^r(x)$, where
the Ducci map $D$ on $\mathbb{Z}_m^n$ sends $(x_1, \dots, x_n)$ to
$(x_1 + x_2, x_2 + x_3, \dots, x_n + x_1)$.
