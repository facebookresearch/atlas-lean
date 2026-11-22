# Partition average sum

For a function $f : \mathbb{R} \to \mathbb{R}$, a real number $p$
and real numbers $t_0, t_1, \dots, t_n$, the partition average sum is

$$\sum_{i=0}^{n-1} (t_{i+1} - t_i)
\left(\frac{1}{t_{i+1} - t_i} \int_{[t_i, t_{i+1}]} |f(x)|\,dx\right)^p,$$

where the integrals are Lebesgue integrals over the closed intervals $[t_i, t_{i+1}]$ (empty when
$t_{i+1} < t_i$), the integral of a function that is not integrable there counts as $0$, $1/0 = 0$,
and $0^p$ is taken to be $1$ when $p = 0$ and $0$ when $p \ne 0$.
