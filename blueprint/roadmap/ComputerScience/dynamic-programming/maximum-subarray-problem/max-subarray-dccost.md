# Cost recurrence of divide-and-conquer maximum subarray

The function
$T : \mathbb{N} \to \mathbb{N}$ given by $T(n) = 0$ for $n \le 1$ and
$T(n) = T(\lfloor n/2 \rfloor) + T(n - \lfloor n/2 \rfloor) + 2n + 3$ for $n \ge 2$.
