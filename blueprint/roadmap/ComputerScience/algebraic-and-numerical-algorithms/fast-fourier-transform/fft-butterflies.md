# FFT butterfly pass

For a commutative ring $R$, an element $\omega \in R$ and vectors
$q, r \in R^m$ and $y \in R^{2m}$, the butterfly pass starts from the state $(1, y)$, applies the
FFT butterfly with $\omega$, $q$ and $r$ at the indices $k = 0, 1, \dots, m - 1$ in increasing
order, and returns the final state; its time cost is the sum of the costs of these $m$
butterflies.
