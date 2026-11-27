# The explicit detuned attaining functional

For each $c\ge40$ let $c'=c-1$. Using the [site count $N$](strip-potential-and-zero-law.md), choose the quantiles $\chi_n>x_*$ with $c'N(\chi_n)=n-1/4$, for $n=2,3,\ldots$; omit site $1$. Keep the simple real site $\chi_2$ and detune every later site by $\epsilon_n=(\chi_{n+1}-\chi_n)/4$. Define the image-charge factor and product in the $b$ variable by

$$
T_\zeta(b)=\tanh\!\left(\frac{\pi(b-\zeta)}2\right)\tanh\!\left(\frac{\pi(b+\zeta)}2\right),
\qquad B(b)=T_{\chi_2}(b)\prod_{n\ge3}T_{\chi_n+i\epsilon_n}(b)T_{\chi_n-i\epsilon_n}(b).
$$

Set $h_0(b)=\operatorname{sech}^2(\pi b/2)B(b)$. This function is even in $b$; for the transform and for the final functional read it in the variable $t=c'b^2/3$. Make the odd combination $g=(h_0-\widehat h_0)/2$ with the [planar radial transform](radial-j0-transform.md), and set $t_\star=c'\chi_2^2/3$. The product is ordered by the quantile index and the transform acts in $t$, not in $b$.

## Depends on

- [Slit strip and zero-law quantiles](strip-potential-and-zero-law.md)
- [Radial transform](radial-j0-transform.md)

## Expansion

Construct the unique quantiles using the strictly increasing site count above $x_*$. Prove the spacing bound that separates the detuned poles from the closed strip at $c\ge40$, and local uniform convergence of the infinite product in a strip containing it. Prove integrability of the real-axis input in the $t$ variable before using the radial Fourier operator. Keep the simple site, conjugate pairs, and outer factor in the same construction.

## Sources

- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [§7.1 and image-charge factor (7.1), p. 37](https://hexagonmath.org/pdf/2611.00174v1#page=37).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [quantiles in §7.2, p. 38](https://hexagonmath.org/pdf/2611.00174v1#page=38).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [(7.4)–(7.5) and Proposition 7.2, p. 39](https://hexagonmath.org/pdf/2611.00174v1#page=39).
