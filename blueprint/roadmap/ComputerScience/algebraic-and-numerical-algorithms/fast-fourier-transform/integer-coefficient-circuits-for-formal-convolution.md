# Near-square-root logarithmic cost for formal convolution over the integers

For every real $\alpha>1/2$ there is a real $C>0$ such that, for every natural $n>0$, there is a division-free arithmetic straight-line program with integer constants on two disjoint lists of $n$ formal variables $X_i,Y_j$. Constants and input registers cost zero; each binary addition, subtraction or multiplication of earlier registers costs one. Designate an available output register for each $0\le d<2n-1$ whose polynomial is

$$
\sum_{0\le i,j<n,\ i+j=d} X_iY_j
$$

as an identity over $\mathbb Z$ in the formal polynomial ring. The total program cost is at most $Cn(1+\log_2 n)^\alpha$, with $C$ fixed before $n$. Specializing the constants and formal identities to any field gives the same bound there. This is not an algorithm uniformly generating the programs, an exact complex scalar-RAM bill, a bound on bitlengths of constants, or a lower bound for batched products.

## Depends on

- The integer arithmetic gate model and the formal convolution coefficients as defined above.

## Proof depends on

- The protected packed circuit constructions at two and at Gaussian dyadic scalars, and descent of the packed circuits to one integral formula with the exact logarithmic overhead.

## Expansion

Formalize the protected reductions and prime tensor kernels, the leakage-free recovery of each coefficient, and the descent that removes all denominators. Track integer arithmetic gate cost before any field specialization.

## Related topics

- [Exact complex linear convolution in a scalar RAM](uniform-exact-linear-convolution-power-saving-ram.md) agrees on the coefficient formula, not the cost model, program quantifiers or coefficient ring.

## Sources

- OpenAI, [Protected inputs and upper bound](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/FiniteFourier/IntegralConvolutionTheorem.lean#L17-L38), [Unfolded integral bound](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/FiniteFourier/IntegralGridInputs.lean#L69-L74), and [Coefficients](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/FiniteFourier/FixedConvolution.lean#L17-L32), [Correctness](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/FiniteFourier/FixedConvolution.lean#L54-L58).
