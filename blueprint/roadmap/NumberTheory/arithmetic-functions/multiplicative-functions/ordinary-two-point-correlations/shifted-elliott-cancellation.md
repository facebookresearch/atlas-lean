# Ordinary corrected Elliott cancellation along distinct shifts

Let $f_1,f_2:\mathbb N\to\mathbb C$ satisfy the product identity $f_j(mn)=f_j(m)f_j(n)$ for
coprime positive $m,n$. Suppose they are one-bounded and at least one is uniformly nonpretentious.
Then for every pair of distinct natural shifts $h_1,h_2$,

$$
\lim_{N\to\infty}\frac1N\sum_{n=1}^{N} f_1(n+h_1)f_2(n+h_2)=0.
$$

The square-root formulation requires $|f_j(n)|\le1$ also at $n=0$ and uses divergence of the
infimum of the square root of the distance. The squared-distance formulation requires the
bound only for positive $n$ and uses the eventually uniform inequality for the squared distance.
The latter does not inspect $f_j(0)$; setting both values at zero to zero does not change any
positive-input hypothesis or the sum. The finite average is zero at $N=0$ in both totalized
formulations and the limit is through the natural numbers.

## Depends on

- [Uniform nonpretentiousness](uniform-nonpretentiousness.md)

## Expansion

Prove cancellation for the ordinary finite sums. Isolate the high-trace decomposition that forces a character–frequency correlation unless the average tends to zero. Establish the equivalence of the squared-distance and square-root formulations, including the harmless choice of function values at zero.

## Sources

- [OrdinaryElliott.lean — `binary_corrected_elliott`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OrdinaryElliott.lean#L33-L40)
- [OrdinaryTwoPointCorrelations.lean — `binary_corrected_elliott`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OrdinaryTwoPointCorrelations.lean#L51-L58)
