# Capped union bound on any invalid synchronizer observation

Let $\iota$ index the observations and $\Omega$ be a sample space with a σ-algebra. For an index $i$
and an outcome $\omega$ let $r_i(\omega)$ be the resolution time, $b_i$ the settling budget,
$y_i(\omega)$ the ideal voltage, $e_i(\omega)$ the noise, $x_i(\omega)$ the observed voltage and
$\beta_i(\omega)$ the expected bit, and let $V_{ol} < V_{il} < V_{ih} < V_{oh}$ be real voltage
levels. Suppose the [settling guarantee](settling-guarantee.md) holds: $x_i = y_i + e_i$, and
whenever $r_i(\omega) \le b_i$ the ideal voltage encodes the expected bit ($y_i(\omega) \le V_{ol}$
for a false bit, $y_i(\omega) \ge V_{oh}$ for a true bit) and
$|e_i(\omega)| < \min(V_{il} - V_{ol}, V_{oh} - V_{ih})$. Let $\iota$ be finite and $\mu$ a
probability measure on $\Omega$, and let every [invalid event](invalid-event.md) be measurable. Let
$c \ge 0$, $\tau > 0$ and $b_i \ge 0$ for every $i$, and suppose every
[budget-expiry event](resolution-exceeds-event.md) has the exponential tail bound
$\mu\{\omega : b_i < r_i(\omega)\} \le c\, e^{-b_i/\tau}$. Then the probability of some invalid
observation satisfies

$$\mu\Bigl(\bigcup_{i \in \iota} \{\omega : x_i(\omega) \text{ is invalid}\}\Bigr)
\le \min\Bigl(1, \sum_{i \in \iota} c\, e^{-b_i/\tau}\Bigr):$$

the [union bound](measure-bi-union-invalid-event-le-sum.md), capped at $1$, the total probability.
No independence between the observations is assumed. The tail bound is a hypothesis, not derived
from a device model, and no deterministic resolution deadline follows from it.
