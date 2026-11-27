# Infection clock: the integrated infection rate along a path

For a real number $\beta$, a natural number $N$, paths $S, I \colon \mathbb{R} \to \mathbb{N}$ and a
time $t \in \mathbb{R}$, the infection clock is

$$\Lambda_1(t) = \max\left(0,\ \int_0^t \frac{\beta\, S(u)\, I(u)}{N}\, du\right),$$

the integrated infection rate, truncated at $0$ so that it is a point of $[0, \infty)$ at which
the driving counting process can be evaluated. It is meant for $\beta \ge 0$, $N \ge 1$, $t \ge 0$
and paths whose integrand is integrable on $[0, t]$ (for example measurable paths bounded by $N$);
there the integral is nonnegative and the truncation does nothing. For other inputs: for $N = 0$
the integrand is $0$ by the convention $x/0 = 0$, so $\Lambda_1(t) = 0$; for $t < 0$ the integral
is the oriented one, $-\int_t^0$; an integrand that is not integrable on the interval gives the
integral $0$; and a negative integral (for example when $t < 0$ and $\beta \ge 0$) gives
$\Lambda_1(t) = 0$.
