# Settling guarantee of a family of synchronizer observations

Let $\iota$ index the observations and $\Omega$ be a sample space with a σ-algebra. For an index $i$
and an outcome $\omega$ let $r_i(\omega)$ be the resolution time, $b_i$ the settling budget,
$y_i(\omega)$ the ideal voltage, $e_i(\omega)$ the additive noise, $x_i(\omega)$ the observed
voltage and $\beta_i(\omega)$ the expected bit, all real except the bit, and let
$V_{il}, V_{ih}, V_{ol}, V_{oh}$ be real voltage levels. The settling guarantee is the conjunction
of:

- $x_i(\omega) = y_i(\omega) + e_i(\omega)$ for every $i$ and $\omega$;
- whenever $r_i(\omega) \le b_i$, the ideal voltage encodes the expected bit in its output band:
  $\beta_i(\omega)$ is false and $y_i(\omega) \le V_{ol}$, or $\beta_i(\omega)$ is true and
  $y_i(\omega) \ge V_{oh}$;
- whenever $r_i(\omega) \le b_i$, the noise is below both noise margins:
  $|e_i(\omega)| < \min(V_{il} - V_{ol}, V_{oh} - V_{ih})$.

Nothing is required when $r_i(\omega) > b_i$. The intended levels satisfy
$V_{ol} < V_{il} < V_{ih} < V_{oh}$, which makes both margins positive. The definition accepts any
reals; if a margin is at most $0$, the third condition holds only when $r_i(\omega) > b_i$ for every
$i$ and $\omega$. The budgets, resolution times and voltages are data supplied by a synchronizer
analysis.
