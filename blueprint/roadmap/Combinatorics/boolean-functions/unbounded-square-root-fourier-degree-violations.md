# Unbounded signed violations of the square-root Fourier-degree bound

For a sign-valued function $f$ on the sign cube of dimension $n$, write $\widehat f(S)=2^{-n}\sum_x f(x)\prod_{i\in S}x_i$ (true corresponds to sign $-1$), and let $\deg(f)$ be the maximum $|S|$ with $\widehat f(S)\ne0$, or zero if no such $S$ exists. For every $C>0$ there exist $n>0$ and a nonconstant sign-valued $f$ with

$$
\sum_i\widehat f(\{i\})>C\sqrt{\deg(f)}.
$$

This is the signed assertion. The separate absolute-ratio statement has a different quantifier over functions: its set includes **all** sign-valued positive-degree functions, without a signed-sum condition.

## Depends on

- Uniform normalized sign-cube Fourier coefficients and maximum nonzero-support degree.

## Proof outline

Track the signed coefficients and positive degree on the constructed family. Prove the Fourier inversion bridge separately. This is an independent clause, not a definition of the admissible functions in the absolute-ratio set.

- Explicit family with a positive signed singleton sum growing beyond each $C\sqrt{\deg(f)}$.

## Sources

- [Comparator statement: `OAI.SquareRootDegree.main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SquareRootDegree.lean#L55-L59)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/192.md)
