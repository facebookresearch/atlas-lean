# Cyclic sum formula for strict multiple zeta values of indices

Let $k = (k_1, \dots, k_l)$
be a nonempty list of positive integers, not all equal to $1$, with subscripts read modulo $l$,
and write $\zeta$ for the strict multiple zeta value. For $1 \le j \le l$ and
$1 \le i \le k_j - 1$ the left-hand index of the cyclic sum formula of $k$ at $(j, i)$ is
$(k_j - i + 1, k_{j+1}, \dots, k_{j+l-1}, i)$, and its right-hand index at $j$ is
$(k_j + 1, k_{j+1}, \dots, k_{j+l-1})$; the run $k_{j+1}, \dots, k_{j+l-1}$ is empty when
$l = 1$. Then

$$
\sum_{j=1}^{l} \sum_{i=1}^{k_j - 1} \zeta(k_j - i + 1, k_{j+1}, \dots, k_{j+l-1}, i)
= \sum_{j=1}^{l} \zeta(k_j + 1, k_{j+1}, \dots, k_{j+l-1}),
$$

where the inner sum is empty when $k_j = 1$.
