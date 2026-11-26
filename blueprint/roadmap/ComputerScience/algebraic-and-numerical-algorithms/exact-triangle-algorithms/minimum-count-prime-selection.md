# A minimum-count prime has few false positives

Let the weights of an Exact Triangle instance with $n$ vertices per part be bounded by $n^\kappa$ with $\kappa \ge 1$, and let $16 \le D \le n$. Let $p^*$ minimize $Z_p$ over the primes $p$ in $[\sqrt{D}/2, \sqrt{D})$. Then $p^*$ also minimizes $F_p$ over that window, and

$$
F_{p^*} \le C\, \kappa\, \frac{n^3 \log n}{\sqrt{D}}
$$

for an absolute constant $C$.

## Proof sketch

$Z_p - F_p = Z$ does not depend on $p$. A nonzero weight of size at most $3n^\kappa$ has at most $O(\kappa \log n / \log D)$ prime divisors in the window, while the window contains $\Omega(\sqrt{D}/\log D)$ primes; averaging the $n^3$ triangles over the window bounds the minimum.

## Depends on

- [Modular triangle counts and false positives](modular-triangle-counts.md)

## Sources

- J. Alman and V. Vassilevska Williams, "Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs", 2026.
