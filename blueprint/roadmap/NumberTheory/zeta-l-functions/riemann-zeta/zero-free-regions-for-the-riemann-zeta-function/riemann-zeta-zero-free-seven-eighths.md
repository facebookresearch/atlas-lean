# The Riemann zeta zero-free half-plane at 7/8

For every complex $s$ with $\operatorname{Re}s>7/8$ and $s\ne1$, the meromorphic continuation of the
Riemann zeta function satisfies $\zeta(s)\ne0$. The pinned statement also includes $s=1$ for the
particular totalized Mathlib function `riemannZeta`: its assigned value there is nonzero. This
assignment is not a value of the meromorphic function at its pole.

## Proof depends on

- [Dirichlet half-plane nonvanishing](../../dirichlet-l-functions/zeros-of-dirichlet-l-functions/dirichlet-l-zero-free-seven-eighths.md)

## Proof outline

Apply the modulus-one principal-character identification away from the pole and handle the library value at the pole independently. The classical logarithmic zero-free region and nonvanishing on the line $\operatorname{Re}s=1$ do not give this whole half-plane.

## Sources

- [QuasiRiemannHypothesis.lean — `riemannZeta_ne_zero_of_seven_eighths_lt_re`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/QuasiRiemannHypothesis.lean#L5-L8)
