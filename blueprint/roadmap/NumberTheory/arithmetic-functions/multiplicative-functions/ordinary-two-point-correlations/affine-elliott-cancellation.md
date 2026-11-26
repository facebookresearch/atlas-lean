# Ordinary corrected Elliott cancellation along affine forms

Let $f_1,f_2:\mathbb N\to\mathbb C$ satisfy $|f_j(n)|\le1$ for every $n>0$ and
$f_j(mn)=f_j(m)f_j(n)$ for coprime positive $m,n$. Suppose at least one of the functions is
uniformly nonpretentious in the squared-distance sense. Given natural $a_1,a_2,b_1,b_2$ with
$a_1,a_2>0$ and $a_1b_2\ne a_2b_1$,

$$
\lim_{N\to\infty}\frac1N\sum_{n=1}^N f_1(a_1n+b_1)f_2(a_2n+b_2)=0
$$

for natural $N\to\infty$. There is no conjugation of $f_2$ in the correlation.

## Depends on

- [Uniform nonpretentiousness](uniform-nonpretentiousness.md)

## Expansion

Separate the conditional cancellation estimate for positive shifts from the reduction for two nonproportional affine forms. Prove the ordinary, not logarithmically weighted, high-trace estimate uniform in the relevant frequency ranges; check the affine reductions preserve the nonpretentious input.

## Sources

- [OrdinaryTwoPointCorrelations.lean — `affine_corrected_elliott`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OrdinaryTwoPointCorrelations.lean#L59-L66)
