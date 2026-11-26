# Uniform exact linear convolution with a logarithmic power saving in a scalar RAM

Use the [typed scalar and index RAM](typed-scalar-and-index-ram.md), including its exact work, peak and validity rules. Both programs are closed: the order program maps a natural word to a natural word, and the solver has the input and output types specified below.

For convolution also allow products between left-input and right-input complex data, storing the product in the distinct combined-data kind. Addition and subtraction preserve kind and scalar multiplication is allowed; products of arbitrary complex data values are not primitives. The root-order preparation remains a program without the product operation.

There exist one fixed order-preparation program, one fixed convolution program, a natural exponent $d$, and a work bound $W:\mathbb N\to\mathbb N$. For each $n>0$, put $P=(n+2)^d$. The valid preparation computes $0<m<1024(2n-1)^3$ with $m\le P$. The valid convolution computation receives $n$, the supplied root $\exp(2\pi i/m)$, and two length-$n$ arrays $x,y$ tagged left and right respectively. It returns the whole combined-tagged length-$(2n-1)$ array with coefficient $\sum_{r+s=k} x_r y_s$ at index $k$, with $0\le r,s<n$. Both peaks are at most $P$, $W(n)+10(n+2)\le P$, and the sum of preparation work, one root-supply charge, and convolution work is at most $W(n)$ for every $x,y$.

Let $\theta=\log(10^6-6871402692000000/2^{71})/\log(10^6)$. The same $W$ satisfies $O(n(\log n)^\theta(\log\log n)^{4-\theta})$, $O(n(\log n)^{1-10^{-13}})$, and $o(n\log n)$ as $n\to\infty$. No requirement identifies its witness programs with those of the transform theorem.

## Depends on

- The [typed scalar and index RAM with its exact accounting rules](typed-scalar-and-index-ram.md), in the indicated modes, and the full linear coefficient sum defined above.

## Proof depends on

- An exact padding and convolution construction with the bilinear kind discipline, verified denominators, fixed-order preparation and the three total-work bounds.

## Expansion

Verify the product kinds, particularly that cross-products are only left-by-right, and that padding/readout returns exactly $2n-1$ coefficients. Bridge the work and address accounting for this code, not merely the number of arithmetic gates in a nonuniform circuit.

## Related topics

- [Coefficients of a product of vector polynomials](fft-polynomial-mul-coeff.md) gives the same linear convolution identity in the vector polynomial setting.

## Sources

- OpenAI, [UniformFourier.lean, typed RAM](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/UniformFourier.lean#L9-L254) and [`ConvProgram`, `TimeBounds` and `convolution_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/UniformFourier.lean#L264-L331).
