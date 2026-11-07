# Limit law of the smallest denominator

For real $x$ and $\delta > 0$ let
$q_{\min}(x, \delta)$ be the smallest positive integer $q$ such that some rational $p/q$ lies in
the open interval $(x - \delta/2, x + \delta/2)$, and let $\eta_{\log}$ be the log smallest
denominator density. Then $\eta_{\log}$ is a probability density on $\mathbb{R}$:
$\eta_{\log}(s) \ge 0$ for every real $s$ and $\int_{-\infty}^{\infty} \eta_{\log}(s) \, ds = 1$.
Moreover, for all real numbers $a$, $b$, $L$ with $0 \le a \le b \le 1$, as $\delta \to 0^+$ the
Lebesgue measure of $\{x \in [a, b] : \log q_{\min}(x, \delta) > L - \tfrac12 \log \delta\}$
tends to $(b - a) \int_L^\infty \eta_{\log}(s) \, ds$.

The interval is taken closed; its endpoints do not affect the measures.

## Sources

- Jens Marklof, *The Log Moments of Smallest Denominators*, INTEGERS 24 (2024), Article A55, Proposition 1 (`integers-2024-A55-prop-1`).
