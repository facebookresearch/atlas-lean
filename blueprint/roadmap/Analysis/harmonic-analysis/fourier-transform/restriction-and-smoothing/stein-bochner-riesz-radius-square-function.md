# Stein's Bochner–Riesz radius square function in the strict range

Let $B_r^\alpha$ be the Euclidean angular-frequency multiplier $(\max(1-(|\xi|/r)^2,0))^\alpha$, with Fourier phase $-ix\cdot\xi$ and inverse phase $+ix\cdot\xi$ and factor $(2\pi)^{-n}$. For a complex Schwartz function $f$ put $S_\alpha f(x)=(\int_0^\infty |r\,\partial_r B_r^\alpha f(x)|^2\,dr/r)^{1/2}$ using a nonnegative integral. For every integer $n\geq2$, finite real $p\geq2$, and real $\alpha>\max(1/2,n(1/2-1/p))$, there is $C>0$ depending only on $n,p,\alpha$ such that $S_\alpha f\in L^p(\mathbb R^n)$ and $\|S_\alpha f\|_p\leq C\|f\|_p$. The source uses the actual real-radius derivative (Lean's totalized derivative), not a formal symbol in its place.

## Depends on

The Bochner–Riesz operator, the pointwise radius derivative and the $dr/r$ square function.

## Proof depends on

Differentiation of the multiplier integral at positive radius and a square-function estimate for the resulting localized singular symbols.

## Expansion

Prove differentiation with the support boundary and exponent loss accounted for, and identify the derivative in the integral. Separate the square integration in radius from the spatial $L^p$ estimate; a bound on each individual radius alone does not control the square integral.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LocalSmoothing.lean#L133-L142) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/079.md).
