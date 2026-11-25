# Upper incomplete gamma function

For real $a$ and $x$, the upper incomplete gamma function is $\Gamma(a, x) = \int_{(x, \infty)} t^{a - 1} e^{-t}\, dt$, with $t^{a-1}$ the real power: the usual power of a positive base, $0^0 = 1$ and $0^s = 0$ for $s \ne 0$, and $t^s = |t|^s \cos(\pi s)$ for $t < 0$. The integral converges for $a > 0$ and $x \ge 0$, and for every $a$ when $x > 0$. When the integrand is not integrable on $(x, \infty)$, for instance for $a \le 0$ and $x = 0$, the integral is read as $0$.

## Idea

The function keeps the tail of the integral defining $\Gamma(a)$: $\Gamma(a, 0) = \Gamma(a)$ for $a > 0$, and $\Gamma(a, x)$ decreases to $0$ as $x \ge 0$ grows. It is the tail of the gamma law. If $X$ has shape $a > 0$ and rate $r > 0$, then $P(X > c) = \Gamma(a, rc)/\Gamma(a)$ for $c \ge 0$. Integration by parts gives $\Gamma(a + 1, x) = x^a e^{-x} + a\,\Gamma(a, x)$ for $a > 0$ and $x \ge 0$. Starting from $\Gamma(1, x) = e^{-x}$, this yields $\Gamma(n + 1, x) = n!\, e^{-x} \sum_{k=0}^{n} x^k/k!$ for natural $n$. So at integer shapes the gamma tail is a finite sum, the Erlang tail formula $P(X > c) = e^{-rc} \sum_{k=0}^{n} (rc)^k/k!$ for shape $n + 1$.

## Statements

- [Upper incomplete gamma function](upper-incomplete-gamma.md)
- [Upper incomplete gamma function at zero](upper-incomplete-gamma-zero.md): basic property: value at $0$
- [Upper incomplete gamma function with shape one](upper-incomplete-gamma-one.md): special case: shape one
- [Recurrence for the upper incomplete gamma function](upper-incomplete-gamma-add-one.md): basic property: recurrence in the shape
- [Upper incomplete gamma function at natural shapes](upper-incomplete-gamma-nat-cast-add-one.md): closed form at natural shapes
- [Upper tail of the gamma law](gamma-measure-real-ioi.md): application: the upper tail of the gamma law
- [Erlang tail formula](gamma-measure-real-ioi-nat-cast-add-one.md): Erlang tail formula at integer shapes

## Sources

- F. W. J. Olver et al. (eds.), *NIST Digital Library of Mathematical Functions*, incomplete gamma functions.
