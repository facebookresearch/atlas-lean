# Recovery clock: the integrated recovery rate along a path

For a real number $\gamma$, a path $I \colon \mathbb{R} \to \mathbb{N}$ and a time
$t \in \mathbb{R}$, the recovery clock is

$$\Lambda_2(t) = \max\left(0,\ \int_0^t \gamma\, I(u)\, du\right),$$

the integrated recovery rate, truncated at $0$ so that it is a point of $[0, \infty)$. It is meant
for $\gamma \ge 0$, $t \ge 0$ and paths with $I$ integrable on $[0, t]$; there the integral is
nonnegative and the truncation does nothing. For other inputs: for $t < 0$ the integral is the
oriented one, $-\int_t^0$; an integrand that is not integrable on the interval gives the integral
$0$; and a negative integral (for example when $t < 0$ and $\gamma \ge 0$, or when $\gamma < 0$
and $t > 0$) gives $\Lambda_2(t) = 0$.
