# An invalid observation has a resolution time beyond its budget

Let $\iota$ index the observations and $\Omega$ be a sample space with a σ-algebra. For an index $i$
and an outcome $\omega$ let $r_i(\omega)$ be the resolution time, $b_i$ the settling budget,
$y_i(\omega)$ the ideal voltage, $e_i(\omega)$ the noise, $x_i(\omega)$ the observed voltage and
$\beta_i(\omega)$ the expected bit, and let $V_{ol} < V_{il} < V_{ih} < V_{oh}$ be real voltage
levels. Suppose the [settling guarantee](settling-guarantee.md) holds: $x_i = y_i + e_i$, and
whenever $r_i(\omega) \le b_i$ the ideal voltage encodes the expected bit ($y_i(\omega) \le V_{ol}$
for a false bit, $y_i(\omega) \ge V_{oh}$ for a true bit) and
$|e_i(\omega)| < \min(V_{il} - V_{ol}, V_{oh} - V_{ih})$. If $x_i(\omega)$ is an
[invalid observation](invalid-observation.md), then $b_i < r_i(\omega)$: an invalid observation can
occur only after its settling budget has expired. This is the contrapositive of
[within budget, not invalid](not-invalid-observation-of-le.md).
