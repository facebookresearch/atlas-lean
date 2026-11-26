# Logarithmic saving for ordinary affine Liouville correlations

Write $\lambda(n)=(-1)^{\Omega(n)}$ for the Liouville function at positive integers. There is a
real $c>0$ such that for every natural $a_1,a_2,b_1,b_2$ with $a_1,a_2>0$ and
$a_1 b_2\ne a_2 b_1$, there is a real $C>0$ such that, for every real $X\ge3$,

$$
\left|\sum_{n=1}^{\lfloor X\rfloor}\lambda(a_1 n+b_1)\lambda(a_2 n+b_2)\right|
  \le \frac{C X}{(\log X)^c}.
$$

The exponent is absolute; the constant $C$ may depend on the forms.

## Expansion

Decompose the quantitative ordinary Liouville estimate into a bound for the relevant finite correlation sums and a uniform log saving before specializing the parameters to a fixed pair of affine forms. A qualitative Elliott limit cannot by itself yield the stated rate.

## Sources

- [OrdinaryTwoPointCorrelations.lean — `liouville_log_saving`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OrdinaryTwoPointCorrelations.lean#L43-L50)
