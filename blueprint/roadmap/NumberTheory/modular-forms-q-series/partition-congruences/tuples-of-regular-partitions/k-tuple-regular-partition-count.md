# Number of $k$-tuples of $\ell$-regular partitions

For natural numbers $\ell$, $k$ and
$n$, the number $T_{\ell,k}(n)$ is defined by recursion on $k$: $T_{\ell,0}(n)$ is $1$ if
$n = 0$ and $0$ otherwise, and

$$T_{\ell,k+1}(n) = \sum_{i=0}^{n} r_\ell(i) \, T_{\ell,k}(n-i),$$

where $r_\ell(i)$ is the number of $\ell$-regular partitions of $i$.

Peeling off the first component in this way, $T_{\ell,k}(n)$ counts the $k$-tuples
$(\lambda_1, \dots, \lambda_k)$ of $\ell$-regular partitions of $n_1, \dots, n_k$ with
$n_1 + \dots + n_k = n$.

## Sources

- Bishnu Paudel, James A. Sellers, and Haiyang Wang, *Extending Recent Work of Nath, Saikia, and Sarma on k-Tuple ℓ-Regular Partitions*, INTEGERS 26 (2026), Article A4, Introduction (definition of `T_{ℓ,k}`).
