# Almost-everywhere convergence of symmetric Fourier sums in L log L

On $\mathbb T=\mathbb R/(2\pi\mathbb Z)$ with normalized Haar measure $m$, let $f:\mathbb T\to\mathbb C$ be almost everywhere strongly measurable with $\int |f|\log(2+|f|)\,dm<\infty$. Write $\widehat f(k)=\int f(x)e^{-ikx}\,dm(x)$. There is one measurable null set $E$ such that for each $x\notin E$ the full sequence $\sum_{k=-N}^{N}\widehat f(k)e^{ikx}$ converges to $f(x)$ as $N\to\infty$. This is ordinary summation, not a Cesàro statement or subsequence assertion.

## Depends on

- [Fourier partial sum](fourier-partial-sum.md), with the normalized Haar convention and symmetric integer indices.

## Proof depends on

An endpoint control for maximal symmetric partial sums on the specified $|f|\log(2+|f|)$ scale and passage from trigonometric polynomials to the full class.

## Expansion

Separate the endpoint finite-sum distribution estimate from the limiting argument. Verify that the logarithmic integrability entails $L^1$ for the coefficients; construct a single exceptional measurable set rather than one set per partial sum.

## Consequences
This implies [Carleson's $L^2$ convergence theorem](carleson-ae-tendsto.md): on the finite-measure circle, $|f|\log(2+|f|)$ is integrable for $f\in L^2$. Pull the almost-everywhere conclusion back from the circle and then use periodicity.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FourierLLogL.lean#L11-L23) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/075.md).
