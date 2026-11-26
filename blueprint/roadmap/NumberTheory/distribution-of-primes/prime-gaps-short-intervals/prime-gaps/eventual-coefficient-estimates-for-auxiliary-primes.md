# Eventual coefficient estimates for the auxiliary prime product

For sufficiently large real $x$, put

$$
Z(x)=\lfloor x^6\rfloor,\qquad L(x)=\frac{x}{(\log x)^5},\qquad
Y(x)=\lfloor e^{L(x)}\rfloor,\qquad P(x)=\prod_{Z(x)<p\le Y(x)}p,\qquad
\beta(x)=\frac1{L(x)}.
$$

The product is over primes, the logarithm is natural, and the floors take natural values. Set the absolute constant

$$
b_0=\frac1{100e^6},\qquad E(b)=e^2+\frac{2e^6\exp(6e^2)}{b},\qquad
C_0=1+E(b_0)+\frac{E(b_0)}{b_0}.
$$

The claim is that eventually $\beta(x)>0$ and the coefficient hypotheses hold for $P(x),\beta(x),C_0$. In particular $P(x)>1$ is squarefree, its divisor coefficients have absolute value at most one, and for **all** $0\le\gamma\le2\beta(x)$ the two bounds $A_{P(x)}(\gamma)\le C_0$ and $A_{P(x)}(\gamma)\le C_0B(P(x))$ hold. There is a common cutoff in $x$ for these assertions.

## Depends on

- [Coefficient and truncation bounds for a simultaneous-root sieve](truncated-sieve-coefficient-estimates.md)

## Expansion

Prove the eventual normalizer bound $B(P(x))\ge b_0$ and the auxiliary-product moment estimates for $0\le\gamma\log Y(x)\le2$. The latter range follows from the cutoff $Y(x)$ and reciprocal tilt. Verify that the coefficient estimate and squarefreeness hold for this same product before assembling the uniform statement.

## Sources

- [Explicit moment constant](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1596-L1601)
- [Auxiliary prime cutoffs and normalizer floor](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1666-L1679)
- [Eventual coefficient-estimate theorem](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L1777-L1854)
