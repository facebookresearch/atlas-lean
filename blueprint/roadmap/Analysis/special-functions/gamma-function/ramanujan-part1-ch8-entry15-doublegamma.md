# Ramanujan's asymptotic expansion of $((x + 1/2)/e^{\psi(x+1)})^{4n}$

For real $x$ let
$\psi(x) = \Gamma'(x)/\Gamma(x)$ and $a(x) = e^{\psi(x+1)}$. Then $a(x) \to \infty$ as
$x \to \infty$, and for every complex number $n$,

$$\left(\frac{x + 1/2}{a(x)}\right)^{4n} = 1 - \frac{n}{6 a(x)^2} +
\frac{10 n^2 + 11 n}{720 a(x)^4} - \frac{70 n^3 + 231 n^2 + 891 n}{90720 a(x)^6} +
O\left(\frac{1}{a(x)^8}\right)$$

as $x \to \infty$ through the real numbers, where the power is the principal complex power.

Proof: Convexity of `log Γ` gives crude digamma bounds. A telescoped centered expansion and
Taylor's formula for the complex exponential then give the stated coefficients and remainder.

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8.
