# Within its budget, an observation is observed as its expected bit

Let $\iota$ index the observations and $\Omega$ be a sample space with a σ-algebra. For an index $i$
and an outcome $\omega$ let $r_i(\omega)$ be the resolution time, $b_i$ the settling budget,
$y_i(\omega)$ the ideal voltage, $e_i(\omega)$ the noise, $x_i(\omega)$ the observed voltage and
$\beta_i(\omega)$ the expected bit, and let $V_{ol} < V_{il} < V_{ih} < V_{oh}$ be real voltage
levels. Suppose the [settling guarantee](settling-guarantee.md) holds: $x_i = y_i + e_i$, and
whenever $r_i(\omega) \le b_i$ the ideal voltage encodes the expected bit ($y_i(\omega) \le V_{ol}$
for a false bit, $y_i(\omega) \ge V_{oh}$ for a true bit) and
$|e_i(\omega)| < \min(V_{il} - V_{ol}, V_{oh} - V_{ih})$. If $r_i(\omega) \le b_i$, then the
[observation](../logic-levels-and-noise-margins/observe.md) of $x_i(\omega)$ is `some`
$\beta_i(\omega)$: within its budget the observed voltage is read as the expected bit. This is the
[noise preservation](../logic-levels-and-noise-margins/observe-noisy-output.md) result applied to
$x_i(\omega) = y_i(\omega) + e_i(\omega)$.
