# Lower bound on the expected time of bucket sort

Let $n \ge 1$ and let
$\omega = (\omega_0, \dots, \omega_{n-1})$ have independent coordinates, each uniformly
distributed on $[0, 1)$. Let $T(\omega)$ be the number of time steps that bucket sort charges
on the array $(\omega_0, \dots, \omega_{n-1})$ if every $\omega_j$ lies in $[0, 1)$, and
$T(\omega) = 0$ otherwise. Then $5n \le \mathbb{E}[T]$.
