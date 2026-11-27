# Koebe-map witnesses for the four Brennan endpoints

Let $k(z)=z/(1-z)^2$ on the open unit disk $\mathbb D$, $W=k(\mathbb D)$ and $g$ its inverse on $W$. The assertion includes that $k$ is holomorphic and injective on $\mathbb D$, with $k(0)=0$ and $k'(0)=1$. The nonnegative Lebesgue-area integrals of $|k'|^{-2}$ and $|k'|^{2/3}$ on $\mathbb D$ are both infinite. On $W$, neither $|g'|^4$ nor $|g'|^{4/3}$ is Lebesgue-area integrable. The inverse, as a function on the domain $W$, is the inverse induced by $k$ restricted to $\mathbb D$; values outside $W$ do not matter.

## Depends on

- [Open unit disk](../riemann-mapping-theorem/unit-disk.md).
- [Normalized univalent functions](../hadamard-products-of-univalent-functions/class-s.md).

## Proof depends on

The forward estimates use the simple zero at $-1$ and order-three pole at $1$ in $k'(z)=(1+z)/(1-z)^3$, both approached within the disk. The inverse estimates use conformal change of variables.

## Expansion

Check normalization and injectivity using the explicit rational map. Prove logarithmic divergence on an interior sector at each of the two boundary points, then transfer the exponents $t=2-s$ to the inverse with the Jacobian $|k'|^2$. Keep the four endpoint obligations distinct within the common sharpness witness.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/BrennanSharp.lean#L36-L38) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/072.md).
