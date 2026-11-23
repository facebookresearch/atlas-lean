# Comparison function for products of binomial coefficients

For natural numbers $a$ and
$b$, let $c = a - b$ if $b \le a$ and $c = 0$ otherwise. The comparison function
$P_{a,b} \colon \mathbb{R} \to \mathbb{R}$ is defined by

$$P_{a,b}(x) = \left(\frac{a^a}{b^b c^c}\right)^{x(x+1)/2} x^{(1/a - a/(bc))/12 - 1/4} \Big/
\left(\frac{2\pi}{e} \cdot \frac{bc}{a} \cdot x\right)^{x/2}.$$

Here $a^a$, $b^b$ and $c^c$ are integer powers with $0^0 = 1$, a quotient with denominator $0$ is $0$,
and the real powers $t^u$ are defined for all real $t$ and $u$ by $t^u = e^{u \log t}$ for $t > 0$,
$0^0 = 1$, $0^u = 0$ for $u \ne 0$, and $t^u = e^{u \log |t|} \cos(\pi u)$ for $t < 0$.

## Sources

- Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients Revisited*, INTEGERS 24 (2024), Article A59, Theorem 6.
