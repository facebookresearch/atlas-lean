# Certified enclosure for a rounded recursive log-likelihood sum

Let $p$ and $n$ be natural numbers and $\ell, \hat\ell, \delta$ real sequences indexed by
$i = 0, \dots, n - 1$, with $|\hat\ell_i - \ell_i| \le \delta_i$ for every $i$: $\ell_i$ is the
exact log-likelihood of site $i$ and $\hat\ell_i$ a computed value. Write $\mathrm{fl}$ for
[rounding](../floating-point-rounding/fl.md) to $p$ bits, to nearest with ties to even and unbounded
exponent, and let $\hat s$ be the recursive rounded sum of $\hat\ell_0, \dots, \hat\ell_{n-1}$,
accumulated from the last term: $\hat s_n = 0$, $\hat s_i = \mathrm{fl}(\hat\ell_i + \hat s_{i+1})$,
$\hat s = \hat s_0$. Then, with $u = 2^{-p}$,

$$
\Bigl|\hat s - \sum_{i<n} \ell_i\Bigr|
\le \bigl((1 + u)^n - 1\bigr) \sum_{i<n} |\hat\ell_i| + \sum_{i<n} \delta_i.
$$

For $p \ge 1$, $u$ is the unit roundoff of $p$-bit binary floating point; the inequality also holds
for $p = 0$, where the rounding map is only a formal extension and not a floating-point format.

## Sources

- N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM (2002), ch. 2.
