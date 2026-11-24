# Bucket sort runs in expected linear time

For each $n$, let
$\omega = (\omega_0, \dots, \omega_{n-1})$ have independent coordinates, each uniformly
distributed on $[0, 1)$. Let $T_n(\omega)$ be the number of time steps that bucket sort charges
on the array $(\omega_0, \dots, \omega_{n-1})$ if every $\omega_j$ lies in $[0, 1)$, and
$T_n(\omega) = 0$ otherwise. Then $\mathbb{E}[T_n] = \Theta(n)$ as $n \to \infty$.
