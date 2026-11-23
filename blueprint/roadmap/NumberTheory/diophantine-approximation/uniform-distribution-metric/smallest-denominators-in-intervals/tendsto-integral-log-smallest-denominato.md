# Convergence of the log moments of smallest denominators

Let $0 \le a \le b \le 1$ be
real numbers and let $n \ge 0$ be an integer. For real $x$ and $\delta > 0$ let
$q_{\min}(x, \delta)$ be the smallest positive integer $q$ such that some rational $p/q$ lies in
the open interval $(x - \delta/2, x + \delta/2)$, and let $\eta_{\log}$ be the log smallest
denominator density. Then, as $\delta \to 0^+$,

$$
\int_a^b \bigl(\log q_{\min}(x, \delta) + \tfrac12 \log \delta\bigr)^n \, dx \to \mu_n \, (b - a),
$$

where $\mu_n = \int_{-\infty}^{\infty} s^n \, \eta_{\log}(s) \, ds$.

The moment $\mu_n$ is an integral over the whole real line: $\eta_{\log}$ has mass $3/\pi^2$ on
$(-\infty, 0]$, so integrating only over $s \ge 0$ would give $\mu_0 = 1 - 3/\pi^2$ instead of
the correct limit $1$.

## Sources

- Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24 (2024), Article A55, Proposition 2.
