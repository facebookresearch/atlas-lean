# Recurrences for sums of squares and sums of triangular numbers

Let $m \ge 1$ be an
integer. For $n \ge 0$, let $r_m(n)$ be the number of $x \in \mathbb{Z}^m$ with
$x_1^2 + \dots + x_m^2 = n$, and let $t_m(n)$ be the number of $x \in \mathbb{Z}_{\ge 0}^m$ with
$\sum_{i=1}^{m} x_i(x_i+1)/2 = n$. Let $\sigma$ be the sum-of-divisors function, and set
$\sigma(j/2) = 0$ when $j$ is odd. Then for every $n \ge 0$,

$$n\,r_m(n) = m \sum_{j=1}^{n} 2(-1)^{j+1}\bigl(\sigma(j) - \sigma(j/2)\bigr)\,r_m(n-j)$$

and

$$n\,t_m(n) = m \sum_{j=1}^{n} \bigl(\sigma(j) - 4\sigma(j/2)\bigr)\,t_m(n-j).$$

## Sources

- Hartosh Singh Bal and Gaurav Bhatnagar, *Glaisher's Divisors and Infinite Products*, Journal of Integer Sequences 27 (2024), Article 24.1.6, Theorem 11 (`jis-2024-24.1.6-thm-11`).
