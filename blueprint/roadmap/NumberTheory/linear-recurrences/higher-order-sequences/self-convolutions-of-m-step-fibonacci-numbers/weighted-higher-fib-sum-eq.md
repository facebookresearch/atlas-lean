# Closed form for weighted sums of an $m$-step Fibonacci sequence

Let $m \ge 1$ and let
$F : \mathbb{Z} \to \mathbb{Q}$ satisfy the $m$-step Fibonacci recurrence
$F_k = F_{k-1} + \dots + F_{k-m}$ for every integer $k$. For every natural number $n$, every
integer $l$ and every rational number $q$ with $q^{m+1} - 2q + 1 \ne 0$, the weighted sum
$S(m,n,l,q) = \sum_{k=0}^{n} q^k F_{k+l}$ equals

$$
\frac{(q-1)\Bigl(q^{n+1}F_{n+l+1} - F_l +
\sum_{i=1}^{m-1}\sum_{j=1}^{i} q^{i+1-j}\bigl(q^{n+1}F_{n+l-j+1} - F_{l-j}\bigr)\Bigr)}
{q^{m+1} - 2q + 1}.
$$

## Sources

- Jan Sedlák and Antonín Slavík, "Walks in Tiled Rectangles and Self-Convolutions of Higher-Order Fibonacci Numbers", Theorem 2.
