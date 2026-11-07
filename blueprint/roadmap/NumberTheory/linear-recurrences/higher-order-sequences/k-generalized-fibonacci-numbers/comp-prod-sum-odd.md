# Convolution of an odd number of consecutive Fibonacci step sequences

Write $F^{(s)}_k$
for the Fibonacci $s$-step numbers, and write $\sum_{K(r,N)}$ for a sum over all
$(k_1, \dots, k_r) \in \mathbb{N}^r$ with $k_1 + \dots + k_r = N$. For all natural numbers
$\ell \ge 1$, $m \ge 1$ and $n \ge \ell(m + \ell - 1)$,

$$
\sum_{K(2\ell+1, n - \ell(m + \ell - 1))} \prod_{j=0}^{2\ell} F^{(m+j)}_{k_{j+1}} =
\sum_{K(\ell+1, n)} F^{(m+2\ell)}_{k_{\ell+1}} \prod_{j=0}^{\ell-1}
\left(F^{(m+2j+1)}_{k_{j+1}} - F^{(m+2j)}_{k_{j+1}}\right).
$$

## Sources

- Robert Frontczak and Karol Gryszka, "General Convolution Sums Involving Fibonacci `m`-Step Numbers", Theorem 35.
