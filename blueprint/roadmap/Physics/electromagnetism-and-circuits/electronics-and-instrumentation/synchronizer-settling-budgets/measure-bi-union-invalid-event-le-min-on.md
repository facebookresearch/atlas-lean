# Capped union bound for equal budgets, $\min(1, N c\, e^{-b/\tau})$

Let $\iota$ index the observations and $\Omega$ be a sample space with a σ-algebra. For an index $i$
and an outcome $\omega$ let $r_i(\omega)$ be the resolution time, $b_i$ the settling budget,
$y_i(\omega)$ the ideal voltage, $e_i(\omega)$ the noise, $x_i(\omega)$ the observed voltage and
$\beta_i(\omega)$ the expected bit, and let $V_{ol} < V_{il} < V_{ih} < V_{oh}$ be real voltage
levels. Suppose the [settling guarantee](settling-guarantee.md) holds: $x_i = y_i + e_i$, and
whenever $r_i(\omega) \le b_i$ the ideal voltage encodes the expected bit ($y_i(\omega) \le V_{ol}$
for a false bit, $y_i(\omega) \ge V_{oh}$ for a true bit) and
$|e_i(\omega)| < \min(V_{il} - V_{ol}, V_{oh} - V_{ih})$. Let $\iota$ be finite with $N$ elements
and $\mu$ a probability measure on $\Omega$, and let every [invalid event](invalid-event.md) be
measurable. Let $c \ge 0$, $\tau > 0$ and $b \ge 0$, let every budget equal $b$, and suppose every
[budget-expiry event](resolution-exceeds-event.md) satisfies
$\mu\{\omega : b < r_i(\omega)\} \le c\, e^{-b/\tau}$. Then

$$\mu\Bigl(\bigcup_{i \in \iota} \{\omega : x_i(\omega) \text{ is invalid}\}\Bigr)
\le \min\bigl(1, N c\, e^{-b/\tau}\bigr),$$

the [capped union bound](any-invalid-measure-le-min-one-sum.md) with equal terms; for $N = 0$ the
bound is $0$.
