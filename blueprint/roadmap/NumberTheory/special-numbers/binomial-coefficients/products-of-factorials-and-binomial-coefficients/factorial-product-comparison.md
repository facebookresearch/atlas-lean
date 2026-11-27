# Comparison function for products of factorials

For a natural number $k$, the comparison
function $P_k \colon \mathbb{R} \to \mathbb{R}$ is defined by

$$P_k(x) = (k^k)^{x(x+1)/2} \left(\frac{2\pi k x}{e}\right)^{x/2} x^{(3k+1)/(12k)}.$$

Here $k^k$ is an integer power with $0^0 = 1$, the exponent $(3k+1)/(12k)$ is $0$ when $k = 0$ (a
quotient with denominator $0$ is $0$), and the real powers $t^u$ are defined for all real $t$ and $u$ by $t^u = e^{u \log t}$ for $t > 0$,
$0^0 = 1$, $0^u = 0$ for $u \ne 0$, and $t^u = e^{u \log |t|} \cos(\pi u)$ for $t < 0$.

## Sources

- Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients Revisited*, INTEGERS 24 (2024), Article A59, Theorem 5.
