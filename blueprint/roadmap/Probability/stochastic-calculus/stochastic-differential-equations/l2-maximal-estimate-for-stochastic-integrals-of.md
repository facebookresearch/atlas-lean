# L2 maximal estimate for stochastic integrals of coefficient differences

Let $B$ be an $(\mathcal F_t)$-Brownian motion, let $\sigma,b:\mathbb R\to\mathbb R$ be Lipschitz with constant $L$, and let $X,Y$ be continuous adapted processes with $\mathbb E\int_0^t(\sigma(X_u)^2+\sigma(Y_u)^2+|X_u-Y_u|^2)\,du<\infty$. Then, with the [$L^2$ Itô integral](../it-integral/ito-integral-2.md),

$$\mathbb E\sup_{s\le t}\Bigl|\int_0^s\bigl(\sigma(X_u)-\sigma(Y_u)\bigr)\,dB_u\Bigr|^2\le4L^2\int_0^t\mathbb E|X_u-Y_u|^2\,du,$$

and, by the Cauchy–Schwarz inequality,

$$\mathbb E\sup_{s\le t}\Bigl|\int_0^s\bigl(b(X_u)-b(Y_u)\bigr)\,du\Bigr|^2\le L^2\,t\int_0^t\mathbb E|X_u-Y_u|^2\,du .$$

## Depends on

- [Itô integral process](../it-integral/ito-integral-2.md)

## Proof depends on

- [Continuous modification of the Itô integral](../it-integral/ito-integral-continuous-modification.md)
- [Optional stopping theorem in continuous time](../../martingales/optional-stopping-theorem/stopped-value-ae-eq-cond-exp-of-le-of-co.md)
- [Doob's $L^2$ maximal inequality in continuous time](../../martingales/doob-s-maximal-inequalities/lintegral-i-sup-sq-le-of-continuous.md)
- [Itô isometry for progressive integrands](../it-integral/lintegral-ito-integral-sq-of-is-progress.md)

## Expansion

A full proof combines [Doob's $L^2$ maximal inequality](../../martingales/doob-s-maximal-inequalities/lintegral-i-sup-sq-le-of-continuous.md) for the continuous martingale $\int_0^\cdot(\sigma(X)-\sigma(Y))\,dB$ with the [Itô isometry](../it-integral/lintegral-ito-integral-sq-of-is-progress.md) and the Lipschitz bound. It should check that a constant $\sigma$ gives $0$, and test the constant with $\sigma(x)=x$ and $X-Y$ deterministic.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Graduate Texts in Mathematics 113, Springer, 1991, <https://link.springer.com/book/10.1007/978-1-4612-0949-2>, Doob inequality and isometry estimate (topic).
