# Cotype of a Banach space and its dual under the approximation property

Let $X$ be a nonzero real Banach space with the approximation property: for every compact $K\subset X$ and $\epsilon>0$ some bounded finite-rank linear operator $S$ has $\|Sx-x\|<\epsilon$ on $K$. Then $X$ is $K$-convex if and only if both $X$ and its continuous real dual have finite cotype. Specifically, $K$-convexity means a uniform bound on $L^2(\{-1,1\}^n;X)$ operator norms of the first Rademacher projection, $f\mapsto\sum_i\varepsilon_i\mathbb E[\varepsilon_i f(\varepsilon)]$, over all $n$; the cube has uniform probability. Finite cotype of a space $E$ means that there exist real $q\ge2$ and $C\ge0$ such that all finite families $(x_i)$ in $E$ satisfy

$$\left(\sum_i\|x_i\|^q\right)^{1/q}\le C\sqrt{\mathbb E\left\|\sum_i\varepsilon_i x_i\right\|^2}.$$

The exponents and constants of $X$ and its dual need not agree.

## Depends on

- [The approximation property](has-approximation-property.md).
- Uniform Rademacher projections and the real-exponent cotype inequality above.

## Proof depends on

- The Banach-space/dual cotype-to-projection estimate under finite-rank approximation, and the converse cotype bounds from uniform Rademacher projection control.

## Expansion

Bridge compact-set approximation quantifiers and the finite sign-cube norm. Isolate the direction using approximation from its converse and track the bounds uniformly in the cube dimension.

## Sources

- OpenAI, [Cotype comparator, mainTarget_proved](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Cotype.lean#L53-L55).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/326.md).
