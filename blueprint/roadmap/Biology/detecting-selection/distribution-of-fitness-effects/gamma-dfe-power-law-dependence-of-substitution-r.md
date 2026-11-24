# Gamma-DFE power law for the F-based substitution rate

Let $u>0$ and let $|s|$ have the canonical
[gamma DFE](gamma-dfe.md), with fixed shape $a>0$ and rate $r>0$.
Use the explicitly defined [F-based deleterious rate model](nearly-neutral-theory-substitution-rate-decrease.md).
The change of variable $y=4Nx$ gives

$$\frac{k_N}u=\frac1{\Gamma(a)}\left(\frac r{4N}\right)^a
\int_0^\infty\frac{y^a}{e^y-1}e^{-ry/(4N)}\,dy.$$

Consequently

$$N^a\frac{k_N}u\longrightarrow
 a\,\zeta(1+a)\left(\frac r4\right)^a\qquad(N\to\infty).$$

Here $a,r$ and the effect distribution are held fixed. This is not an
$a\to0$ neutral-atom limit, nor an unproved uniform finite-population
approximation. For $a=0.4,r=2$ the constant is approximately $0.9414$.

## Depends on

- [Gamma distribution of fitness effects](gamma-dfe.md)
- [F-based deleterious rate model](nearly-neutral-theory-substitution-rate-decrease.md)

## Expansion

For $y>0$, expand $(e^y-1)^{-1}=\sum_{m\ge1}e^{-my}$.
Tonelli, positivity and the substitution $v=my$ give
$\int_0^\infty y^a/(e^y-1)\,dy
=\Gamma(a+1)\sum_{m\ge1}m^{-(a+1)}
=\Gamma(a+1)\zeta(a+1)$.
It is finite because $a>0$: the integrand behaves as $y^{a-1}$ near
zero and has exponential decay at infinity. This derives the
Bose–Einstein integral instead of using it as an unexplained prerequisite.
The factor $e^{-ry/(4N)}$ increases to one, so monotone convergence
and $\Gamma(a+1)=a\Gamma(a)$ give the limit.

Reuse the canonical gamma and zeta functions and their integral/series
APIs, not new definitions: `Real.integral_rpow_mul_exp_neg_mul_Ioi`
in `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean` and
`zeta_eq_tsum_one_div_nat_add_one_cpow` in
`Mathlib/NumberTheory/LSeries/RiemannZeta.lean` provide the component
identities, specialized to the positive real argument $a+1>1$.

## Sources

- T. Ohta, "Slightly deleterious mutant substitutions in evolution", Nature 246 (1973), 96–98, <https://doi.org/10.1038/246096a0> (not opened). The limit and its constant are derived above.
