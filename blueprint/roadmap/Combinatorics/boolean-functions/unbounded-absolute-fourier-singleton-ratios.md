# Unbounded absolute Fourier singleton sums relative to square-root degree

For dimension $n>0$, let $f$ range over **all** functions from the sign cube $\{-1,1\}^n$ to $\{-1,1\}$ with positive Fourier degree. For $S\subseteq\{1,\ldots,n\}$ set $\widehat f(S)=2^{-n}\sum_x f(x)\prod_{i\in S}x_i$, and let $\deg(f)$ be the largest $|S|$ with $\widehat f(S)\ne0$ (zero for an empty maximum). The set of real ratios

$$
\left\{\frac{\sum_i|\widehat f(\{i\})|}{\sqrt{\deg(f)}} : n>0,\quad f:\{-1,1\}^n\to\{-1,1\},\quad \deg(f)>0\right\}
$$

is unbounded above. Membership in this set does not require a signed violation or a positive signed singleton sum.

## Depends on

- Normalized Boolean Fourier coefficients on the finite sign cube and maximum nonzero-support degree.

## Proof depends on

- [Unbounded signed violations of the square-root degree bound](unbounded-square-root-fourier-degree-violations.md).

## Proof outline

Use a signed witness for each positive bound and prove its degree is positive. Then compare its signed sum with the absolute sum, while keeping the ratio set defined over the full source domain of positive-degree sign functions. No additional assumption on that set is needed.

- Fourier inversion, ensuring that a nonconstant function has positive degree, and the elementary signed-to-absolute sum inequality.

## Sources

- [Signed and absolute comparator definitions and theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SquareRootDegree.lean#L40-L59).
