# Bounded coefficients of the reciprocal of a root-stable polynomial

Let $\rho(z) = \alpha_k z^k + \cdots + \alpha_1 z + \alpha_0$ be a polynomial with $\alpha_k \ne 0$ whose zeros lie in the closed unit disc, those on the unit circle being simple (the [root condition](root-condition.md)). Define $\gamma_0, \gamma_1, \gamma_2, \dots$ by the power series expansion at $z = 0$

$$\frac{1}{\alpha_k + \alpha_{k-1} z + \cdots + \alpha_0 z^k} = \gamma_0 + \gamma_1 z + \gamma_2 z^2 + \cdots.$$

Then $\Gamma = \sup_{l \ge 0} |\gamma_l| < \infty$.

The denominator is $\hat\rho(z) = z^k \rho(1/z)$, whose zeros are the reciprocals of the nonzero zeros of $\rho$. So $1/\hat\rho$ is holomorphic in the open unit disc, with at most simple poles on the unit circle. Subtracting the principal parts $A_i/(z - z_i^{-1})$ leaves a function bounded on the closed disc, whose Taylor coefficients are bounded by Cauchy's estimate; the principal parts have bounded coefficients $-A_i z_i^{l+1}$.

## Depends on

- [Root condition](root-condition.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.4.2, Lemma 1 and its proof. <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
