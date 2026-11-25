# An exponential tail bound on budget expiry bounds the invalid event

Let $\iota$ index the observations and $\Omega$ be a sample space with a σ-algebra. For an index $i$
and an outcome $\omega$ let $r_i(\omega)$ be the resolution time, $b_i$ the settling budget,
$y_i(\omega)$ the ideal voltage, $e_i(\omega)$ the noise, $x_i(\omega)$ the observed voltage and
$\beta_i(\omega)$ the expected bit, and let $V_{ol} < V_{il} < V_{ih} < V_{oh}$ be real voltage
levels. Suppose the [settling guarantee](settling-guarantee.md) holds: $x_i = y_i + e_i$, and
whenever $r_i(\omega) \le b_i$ the ideal voltage encodes the expected bit ($y_i(\omega) \le V_{ol}$
for a false bit, $y_i(\omega) \ge V_{oh}$ for a true bit) and
$|e_i(\omega)| < \min(V_{il} - V_{ol}, V_{oh} - V_{ih})$. Let $\mu$ be a probability measure on
$\Omega$, $c$ and $\tau$ reals and $i$ an index. If the
[budget-expiry event](resolution-exceeds-event.md) of $i$ satisfies

$$\mu\{\omega : b_i < r_i(\omega)\} \le \max\bigl(c\, e^{-b_i/\tau}, 0\bigr),$$

then its [invalid event](invalid-event.md), which it contains, satisfies the same bound:
$\mu\{\omega : x_i(\omega) \text{ is invalid}\} \le \max(c\, e^{-b_i/\tau}, 0)$, the outer measure
if the event is not measurable. The bound is the value of $c\, e^{-b_i/\tau}$ in $[0, \infty]$, with
a negative value clamped to $0$; with the convention $a / 0 = 0$, $\tau = 0$ gives $e^0 = 1$ and the
bound $\max(c, 0)$. In the intended reading $c \ge 0$ and $\tau > 0$, a tail decaying exponentially
in the budget.
