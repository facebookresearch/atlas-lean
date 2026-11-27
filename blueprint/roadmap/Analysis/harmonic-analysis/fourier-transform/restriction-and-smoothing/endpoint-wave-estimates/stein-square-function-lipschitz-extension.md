# Lipschitz extension of the Stein square function to finite Lp

Fix a natural $n\ge2$, a finite extended nonnegative real exponent $p$ with $p\ge2$, and real $\alpha>\max(1/2,n(1/2-1/p))$. There exists a map from complex $L^p(\mathbb R^n)$ to real $L^p(\mathbb R^n)$, both with Lebesgue measure, with a strictly positive Lipschitz constant and taking zero to zero. On the $L^p$ class of every complex Schwartz $f$, its value agrees almost everywhere with the real conversion of the nonnegative Stein square function

$$
S_\alpha f(x)=\left(\int_0^\infty |\mathcal F^{-1}[m_{\alpha,r}\widehat f](x)|^2\,\frac{dr}{r}\right)^{1/2},\qquad
m_{\alpha,r}(\xi)=\begin{cases}2\alpha (|\xi|^2/r^2)(1-|\xi|^2/r^2)^{\alpha-1},&|\xi|<r,\\0,&|\xi|\ge r.\end{cases}
$$

The radius integral is extended nonnegative, and conversion to a real takes infinity to zero. The statement is existence of this extension data (not linearity, and not an additional uniqueness conjunct).

## Depends on

- [Angular-frequency transform](angular-frequency-wave-multipliers.md).

## Proof depends on

- [Stein square-function bound on Schwartz data](../stein-bochner-riesz-radius-square-function.md), after identifying the literal radius derivative with the angular multiplier written above.

## Proof outline

Use the triangle inequality in the radius-variable $L^2$ space to obtain a difference estimate and extend by density of Schwartz functions in finite $L^p$.

Verify the radius square function is finite almost everywhere before passing to the real conversion, then extend the zero-preserving Lipschitz map from the dense domain. The displayed estimate alone is a different endpoint.

## Sources

- OpenAI Math, [`stein_square_fullLp`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/SquareFunction/Main.lean#L22-L24).
- [Named Fourier main-results bundle](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Main.lean#L11-L21).
- [Family scope and accompanying paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/079.md).
- [Definitions in `Definitions.lean`, lines 21–53](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/LocalSmoothing/Definitions.lean#L21-L53).
- [Definitions in `Definitions.lean`, lines 12–24](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/SquareFunction/Definitions.lean#L12-L24).
- [Definitions in `Main.lean`, lines 16–20](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/SquareFunction/Main.lean#L16-L20).
- [Definitions in `Extension.lean`, lines 11–20](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/SquareFunction/Square/Extension.lean#L11-L20).
- [Definitions in `ExtensionDifference.lean`, lines 8–11](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/SquareFunction/Square/ExtensionDifference.lean#L8-L11).
- [Definitions in `Basic.lean`, lines 8–11](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/Wave/Basic.lean#L8-L11).
- [Radius differentiation and the literal square-function comparison](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Analysis/Fourier/SquareFunction/Square/Literal.lean#L14-L36).
