# Uniform exact positive-sign DFT with a logarithmic power saving in a scalar RAM

Use the [typed scalar and index RAM](typed-scalar-and-index-ram.md), including its exact work, peak and validity rules. Both programs are closed: the order program maps a natural word to a natural word, and the solver has the input and output types specified below. Both use linear mode, with scalar and left-tagged complex data and no cross-product primitive.

There exist one fixed order-preparation program, one fixed transform program, a natural exponent $d$, and a work bound $W:\mathbb N\to\mathbb N$, all fixed before the input size. For every $n>0$, with cap $P=(n+2)^d$, preparation on $n$ is valid and computes an order $0<m<1024 n^3$ with $m\le P$. Both work evaluations are valid with their peak natural values at most $P$, and $W(n)+10(n+2)\le P$. The transform program takes $n$, the supplied canonical root $\exp(2\pi i/m)$ and the length-$n$ left-tagged array $x$; it returns exactly the length-$n$ left-tagged array with entry $\sum_k\exp(2\pi i/n)^{jk}x_k$ at index $j$. Preparation work plus one root-supply charge plus transform work is at most $W(n)$ for every $x$.

Let $M=10^6$, $D=6871402692000000$, and $\theta=\log(M-D/2^{71})/\log M$. As $n\to\infty$, $W(n)$ is simultaneously $O(n(\log n)^\theta(\log\log n)^{4-\theta})$, $O(n(\log n)^{1-10^{-13}})$, and $o(n\log n)$.

## Depends on

- [Finite DFT sum](dft-sum.md), with the positive canonical character, and the [typed scalar and index RAM with its exact accounting rules](typed-scalar-and-index-ram.md).

## Proof depends on

- A uniform order-selection and transform construction, exactness and scalar denominator checks, and the work and peak-value recurrence with the supplied-root charge.

## Expansion

Build a verified bridge from the typed scalar/index language to a fixed costed machine. Track both peak natural magnitudes and overall address/arena cost; prove the work bound without charging only data multiplications or silently admitting arbitrary roots as gate literals. Connect the recurrence to each of the three stated asymptotic comparisons.

## Sources

- OpenAI, [UniformFourier.lean, exact scalar/index RAM](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/UniformFourier.lean#L9-L254) and [`DFTProgram`, `TimeBounds` and `transform_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/UniformFourier.lean#L264-L327).
