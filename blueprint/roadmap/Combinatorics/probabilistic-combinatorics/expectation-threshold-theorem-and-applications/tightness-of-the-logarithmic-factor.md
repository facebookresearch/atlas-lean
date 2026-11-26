# The logarithmic factor in the Park-Pham theorem is necessary

The factor $\log \ell(\mathcal{F})$ in the Park-Pham theorem cannot be removed: for the property that $G(n,p)$ has no isolated vertices, $\ell = \Theta(n)$, $q = \Theta(1/n)$ and $p_c = \Theta(\log n/n)$, so $p_c/q = \Theta(\log \ell)$. Combined with $q \le p_c$, the theorem determines $p_c$ up to a $\Theta(\log\ell)$ window for every increasing property.

## Proof sketch

Every member contains an edge at a fixed vertex $v$, so the $n - 1$ singleton edges at $v$ form a cover of cost $(n-1)p$, giving $q \ge 1/(2n)$; conversely a first-moment computation over covers shows the property is not $p$-small for $p = C/n$. The threshold $\log n/n$ for no isolated vertices is classical (Erdős-Rényi).

## Depends on

- [Park-Pham theorem: thresholds are within a logarithmic factor of expectation thresholds](park-pham-theorem.md)
- [The Kahn-Kalai expectation threshold q(F)](kahn-kalai-expectation-threshold.md)

## Proof depends on

- [The expectation threshold is a lower bound on the threshold](expectation-threshold-lower-bounds-the-threshold.md)

## Sources

- Jeff Kahn, Gil Kalai, "Thresholds and expectation thresholds", Combinatorics, Probability and Computing 16(3) (2007).
- Jinyoung Park, Huy Tuan Pham, "A proof of the Kahn-Kalai conjecture", Journal of the AMS 37(1) (2024); arXiv:2203.17207.
