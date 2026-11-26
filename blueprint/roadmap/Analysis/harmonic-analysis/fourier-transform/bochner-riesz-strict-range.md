# Uniform Bochner–Riesz bounds in the strict range

For each integer $n\geq2$, exponent $1\leq p\leq\infty$ and real $\delta>\max(n|1/p-1/2|-1/2,0)$, with $1/\infty=0$, there is a real $C>0$ with the following property. For every $R>0$ and complex Schwartz $f$ on $\mathbb R^n$, $B_R^\delta f\in L^p$ and $\|B_R^\delta f\|_p\leq C\|f\|_p$. The operator is the angular-frequency multiplier $(\max(1-(|\xi|/R)^2,0))^\delta$, using forward phase $-ix\cdot\xi$ and inverse phase $+ix\cdot\xi$ with factor $(2\pi)^{-n}$. One $C$ works at every radius.

## Depends on

Fourier multipliers on Schwartz data and the extended exponent $p$, including essential supremum at infinity.

## Proof depends on
- [Euclidean half-wave local smoothing](euclidean-half-wave-local-smoothing.md), for the strict-range multiplier estimates.

The radial dilation identity and duality/interpolation must preserve bounds at the declared exponents, including $p=\infty$.

## Expansion

Decompose the multiplier into the smooth interior part and bands approaching $|\xi|=R$. State the bound for an individual band and the summability allowed by the strict inequality; transport the normalization to every radius and check the $L^1$ and $L^\infty$ cases separately.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LocalSmoothing.lean#L98-L107) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/079.md).
