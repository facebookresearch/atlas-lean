# The slit-strip extremal potential and zero law

Write $c'=c-1$, $x_*=\operatorname{arsinh}(1)/\pi$, $S=\{b=x+iy:|y|<1/2\}$, and $L(x)=2\pi|x|/3$. Let $D$ be $S$ minus the two real slits $|x|\ge x_*$. For $c\ge40$ use the variable $t=c'b^2/3$. The potential $U$ is the harmonic function on $D$, continuous to the horizontal edges and both lips and tips of the slits, zero on the edges, equal to $-L(x)$ on the slits, and of at most linear growth in $|x|$. Extend it across each slit by that boundary value. Equivalently, put $p(b)=\pi^{-1}\operatorname{arsinh}(-i\sinh(\pi b))$ on the principal branch and

$$
U(b)=U_0+\frac{4\pi}{3}\operatorname{Im}\int_0^b p(z)\,dz,
\qquad U_0=-L(x_*)+\frac43\int_0^{x_*}\arcsin(\sinh(\pi s))\,ds.
$$

The path is in $D$. Its zero law is the measure $(2\pi)^{-1}\Delta U$ in the strip, supported on the real slits with density

$$
\rho_U(x)=\frac{4}{3\pi}\operatorname{arcosh}(\sinh(\pi|x|)),\qquad |x|\ge x_*.
$$

On the right slit the site count $N(x)=\frac12\int_{x_*}^x\rho_U(s)\,ds$ satisfies $N(x)\sim\kappa_{\mathrm{tip}}(x-x_*)^{3/2}$ as $x\downarrow x_*$, where $\kappa_{\mathrm{tip}}=4\,2^{3/4}/(9\sqrt\pi)$. The half converts multiplicity-counted zeros to sites. On $0<\delta\le x_*$ the Cardy deficit is

$$
\kappa(\delta)=-(U+L)(x_* - \delta)=\frac{4}{3}\int_{x_* - \delta}^{x_*}\bigl[\pi/2-\arcsin(\sinh(\pi s))\bigr]\,ds.
$$

## Expansion

Verify holomorphy of the chosen inverse-hyperbolic branch on the strip minus the two slits, path independence and continuity at the lips and tips. Prove the boundary values and uniqueness using the growing strip barrier. Identify the distributional Laplacian by the jump in normal derivative and then derive the tip expansion and deficit. These are concrete potential-theory inputs, not assumptions about a semiclassical spectral curve.

## Sources

- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [(2.17)–(2.18), p. 12](https://hexagonmath.org/pdf/2611.00174v1#page=12).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Lemma 6.5, (6.16)–(6.18), p. 32](https://hexagonmath.org/pdf/2611.00174v1#page=32).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Definition 6.6 and (6.21)–(6.22), p. 34](https://hexagonmath.org/pdf/2611.00174v1#page=34).
- Claude (Anthropic), *The spinless modular bootstrap at large central charge*, version 1 (November 2026), [Lemma 6.7 and (6.24), p. 35](https://hexagonmath.org/pdf/2611.00174v1#page=35).
