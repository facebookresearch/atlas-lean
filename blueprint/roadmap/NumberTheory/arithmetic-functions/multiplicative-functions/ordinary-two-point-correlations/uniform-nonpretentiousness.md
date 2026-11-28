# Uniform nonpretentiousness against character twists

For $f:\mathbb N\to\mathbb C$, a Dirichlet character $\chi$ modulo $q>0$, and $t\in\mathbb R$, put

$$
D_f(\chi,t;N)=\sum_{p\le N\;\mathrm{prime}}
  \frac{1-\operatorname{Re}\bigl(f(p)\overline{\chi(p)\exp(it\log p)}\bigr)}{p}.
$$

Uniform nonpretentiousness means that for every fixed $q>0$, every character $\chi$ modulo $q$,
and every real $K$, there is a natural $N_0$ such that for each natural $N\ge N_0$ and every
$t\in[-N,N]$, one has $D_f(\chi,t;N)\ge K$. The square-root version uses
$\inf_{|t|\le N}\sqrt{D_f(\chi,t;N)}\to+\infty$ for each such $q,\chi$. For functions bounded
in modulus by $1$ at positive integers, $D_f$ is nonnegative and the formulations are equivalent.

## Expansion

Prove nonnegativity from the norm bound on prime inputs and the character norm bound, and prove the equivalence using the nonempty compact frequency interval and monotonicity and unboundedness of the square root. Multiplicativity in the results below means only the coprime product identity at positive integers; do not impose a value at $1$ as part of the definition.

## Sources

- [OrdinaryElliott.lean — `binary_corrected_elliott`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OrdinaryElliott.lean#L33-L40)
- [OrdinaryTwoPointCorrelations.lean — `binary_corrected_elliott`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OrdinaryTwoPointCorrelations.lean#L51-L58)
- [OrdinaryTwoPointCorrelations.lean — `affine_corrected_elliott`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OrdinaryTwoPointCorrelations.lean#L59-L66)
- [Source square-root distance and uniform infimum](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OrdinaryElliott.lean#L11-L28)
- [Source squared distance and uniform eventual quantifiers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/OrdinaryTwoPointCorrelations.lean#L19-L36)
