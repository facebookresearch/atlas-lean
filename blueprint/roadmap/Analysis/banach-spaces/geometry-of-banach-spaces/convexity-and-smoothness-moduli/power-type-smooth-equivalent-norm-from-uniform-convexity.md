# Power-type smooth equivalent norm from uniform convex renormability

Let $X$ be a real Banach space. An equivalent norm here is a real seminorm $N$ with $a\|x\|\le N(x)\le b\|x\|$ for some $a,b>0$ and all $x$. Suppose there exists such a norm $N_0$ that is uniformly convex: for every $0<\varepsilon\le2$ there is $\delta>0$ such that $N_0((x+y)/2)\le1-\delta$ whenever $N_0(x),N_0(y)\le1$ and $N_0(x-y)\ge\varepsilon$.

Then there exist an equivalent norm $N$, real $1<q\le2$, and one real $C>0$ such that

$$
\frac{N(x+y)^q+N(x-y)^q}{2}\le N(x)^q+C N(y)^q\qquad(x,y\in X).
$$

For $N(x)=N(y)=1$ and every $t\ge0$ one also has

$$
\frac{N(x+ty)+N(x-ty)}2\le1+Ct^q.
$$

The modulus $\rho_N(t)$ is the supremum of zero and the values $[N(x+ty)+N(x-ty)]/2-1$ over these unit vectors. It satisfies $\rho_N(t)\le Ct^q$ for all $t\ge0$. The same $N$ is uniformly smooth: for every $\varepsilon>0$ some $\delta>0$ makes the unit-vector average at most $1+\varepsilon t$ for $0<t<\delta$. No simultaneous uniform convexity of the output norm is asserted. The zero space is allowed, with modulus zero when there are no unit vectors.

## Depends on

Positive equivalence bounds for seminorms on the same real vector space, closed-unit-ball uniform convexity, and the inserted-zero supremum convention for smoothness.

## Proof depends on

A finite upper martingale estimate extracted from uniform convex renormability, extrapolation to finite dyadic martingale type, and construction of an equivalent norm realizing the symmetric power estimate.

## Expansion

Separate the structural finite upper $L^2$ estimates from dyadic extrapolation and the norm construction. Use the same exponent and constant for the symmetric estimate, the unit-vector inequality and modulus bound, and then deduce uniform smoothness. Do not substitute an arbitrary uniformly smooth norm without power control.

## Sources

- G. Pisier, *Martingales with values in uniformly convex spaces*, Israel Journal of Mathematics **20** (1975), 326–350, [doi:10.1007/BF02760337](https://doi.org/10.1007/BF02760337). This is the classical power-type renorming theorem cited by the accompanying paper.
- OpenAI Math, [`exists_power_smooth_equivalentNorm`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/MarkovType/PisierPowerRenorming.lean#L14-L18).
- [Family scope and accompanying paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/327.md).
- [Definitions in `Main.lean`, lines 22–37](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/MarkovType/Main.lean#L22-L37).
- [Definitions in `PisierPowerRenorming.lean`, lines 10–12](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/MarkovType/PisierPowerRenorming.lean#L10-L12).
- [Definitions in `RenormingBasic.lean`, lines 11–20](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/MarkovType/RenormingBasic.lean#L11-L20).
- [Definitions in `RenormingBasic.lean`, lines 49–63](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/MarkovType/RenormingBasic.lean#L49-L63).
- [Definitions in `SmoothnessBounds.lean`, lines 19–34](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/MarkovType/SmoothnessBounds.lean#L19-L34).
