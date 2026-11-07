# Convolution of four consecutive Fibonacci step sequences

Write $F^{(s)}_k$ for the
Fibonacci $s$-step numbers, and write $\sum_{K(4,N)}$ for a sum over all
$(k_1, k_2, k_3, k_4) \in \mathbb{N}^4$ with $k_1 + k_2 + k_3 + k_4 = N$. For all natural numbers
$m \ge 1$ and $n \ge 2m + 2$,

$$
\sum_{K(4, n - 2m - 2)} F^{(m)}_{k_1} F^{(m+1)}_{k_2} F^{(m+2)}_{k_3} F^{(m+3)}_{k_4} =
\sum_{j=0}^{n} \left(F^{(m+3)}_j - F^{(m+2)}_j\right) \left(F^{(m+1)}_{n-j} - F^{(m)}_{n-j}\right).
$$

The paper prints the index of the last factor on the left as $k_3$; it is corrected to $k_4$
here.

## Sources

- Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving Fibonacci `m`-Step Numbers", Theorem 34.
