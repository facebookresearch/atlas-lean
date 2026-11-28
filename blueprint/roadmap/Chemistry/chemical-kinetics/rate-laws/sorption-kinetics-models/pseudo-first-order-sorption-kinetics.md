# Pseudo-first-order sorption kinetics

The pseudo-first-order (Lagergren) model of batch uptake is $dq/dt = k_1(q_e - q)$, $q(0) = 0$, with linear form $\ln(q_e - q_t) = \ln q_e - k_1t$.

Let $q_t$ be the uptake at time $t \ge 0$ in a batch sorption experiment, measured in a fixed unit, with equilibrium
uptake $q_e > 0$ and rate constant $k_1 > 0$ (inverse time). The pseudo-first-order model is the initial-value problem

$$
\frac{dq_t}{dt} = k_1(q_e - q_t), \qquad q_0 = 0,
$$

whose unique solution on $t \ge 0$ is $q_t = q_e(1 - e^{-k_1t})$. Hence $0 \le q_t < q_e$ for every $t \ge 0$,
$q_t \to q_e$ only as $t \to \infty$, and the source's linear form holds for all $t \ge 0$:

$$
\ln(q_e - q_t) = \ln q_e - k_1 t ,
$$

where both logarithms are taken of numerical values in the same uptake unit (equivalently
$\ln(1 - q_t/q_e) = -k_1t$). Fitting the linear form requires $q_e$ to be fixed in advance or estimated iteratively;
it is not an unconditional two-parameter linear regression.

## Context

Undergraduate level. With the pseudo-second-order model, this is the routine kinetic analysis in dye and metal-ion uptake studies on metal–organic frameworks; a good fit is a descriptive statement, not a mechanism.

## Depends on

None.

## Proof depends on

- [Uniqueness of the first-order solution](../first-order-sol-unique.md)

## Expansion

With $y = q_e - q_t$ the problem becomes $y' = -k_1y$, $y(0) = q_e$, whose unique solution is $q_e e^{-k_1t}$ by the
first-order uniqueness result; taking logarithms of $y > 0$ gives the linear form. This sorption model is distinct
from the [pseudo-first-order approximation](../pfo-sol.md) of a bimolecular reaction with one reagent in
excess.

## Sources

- S. Gazvineh, M. Adeli and M. Nemati, "Metal-organic frameworks with linear and branched polyol backbones for dye removal", *Scientific Reports* (2026), [doi.org](https://doi.org/10.1038/s41598-026-37325-0), Eqn (3).
