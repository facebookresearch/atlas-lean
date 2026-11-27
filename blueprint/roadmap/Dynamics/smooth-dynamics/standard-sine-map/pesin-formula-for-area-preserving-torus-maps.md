# Pesin’s entropy formula for smooth area-preserving torus maps

Let $F$ be a $C^\infty$ diffeomorphism of the flat two-torus preserving normalized area $m$. The two Lyapunov exponents, counted with multiplicity, exist $m$-almost everywhere and are $\lambda_+(z)$ and $-\lambda_+(z)$, with $\lambda_+(z)\ge0$. Then the Kolmogorov–Sinai entropy with natural logarithms satisfies

$$ h_m(F)=\int_{\mathbb T^2}\lambda_+(z)\,dm(z). $$

This version does not require that $F$ be ergodic or that its exponents be nonzero. Compactness and smooth invertibility bound the derivative/inverse-derivative logarithms needed for the multiplicative ergodic theorem, and determinant of absolute value one gives the opposite exponents.

## Depends on

- [Kolmogorov–Sinai entropy](../../ergodic-theory/kolmogorov-sinai-entropy/ks-entropy.md)

## Expansion

Define the measurable largest Lyapunov exponent on the conull Oseledets set and show its integrability. Extend the entropy formula to the compact manifold and area probability in this statement; the planar ergodic specialization has extra hypotheses and cannot be applied directly. Verify the natural-log normalization and the determinant-one exponent relation.

## Related results

- [Pesin’s entropy formula in the planar ergodic setting](../entropy-dimension-and-lyapunov-exponents/pesin-formula.md): for a diffeomorphism of the plane and an ergodic probability measure under additional dimension and exponent assumptions. It is not a proof prerequisite for the torus statement.

## Sources

- [Application of the absolutely continuous Pesin entropy formula in the standard-map argument](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Positive-Metric-Entropy-for-the-Standard-Map-at-Large-Parameters-September-23-2026/build/sections/introduction.tex#L70-L85).
- Ya. B. Pesin, “Characteristic Lyapunov exponents and smooth ergodic theory,” Russian Math. Surveys 32 (1977), 55–114. <https://doi.org/10.1070/RM1977v032n04ABEH001639>
