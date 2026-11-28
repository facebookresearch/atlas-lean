# Pseudo-second-order sorption kinetics

The pseudo-second-order model of batch uptake is $dq/dt = k_2(q_e - q)^2$, $q(0) = 0$, with linear form $t/q_t = 1/(k_2q_e^2) + t/q_e$.

Let $q_t$ be the uptake at time $t \ge 0$, in a fixed unit, with equilibrium uptake $q_e > 0$ and rate constant
$k_2 > 0$ (inverse of uptake times time). The pseudo-second-order model is the initial-value problem

$$
\frac{dq_t}{dt} = k_2(q_e - q_t)^2, \qquad q_0 = 0 .
$$

Among solutions with $q_t < q_e$ on $t \ge 0$ it has the unique solution $q_t = k_2q_e^2t/(1 + k_2q_et)$, whose
initial slope is $k_2q_e^2$. For $t > 0$ this is equivalent to the source's linear form

$$
\frac{t}{q_t} = \frac{1}{k_2q_e^2} + \frac{t}{q_e} .
$$

In a linear fit of $t/q_t$ against $t$ the slope is $1/q_e$ and the intercept $1/(k_2q_e^2)$, so
$k_2 = \text{slope}^2/\text{intercept}$ requires both fitted quantities.

## Context

Undergraduate level. Better pseudo-second-order fits are commonly read as chemisorption-limited uptake in frameworks; the fit alone does not establish the mechanism.

## Depends on

None.

## Proof depends on

- [Uniqueness of the 2A → P solution](../second-order-aasol-unique.md)

## Expansion

With $y = q_e - q_t$ the problem is $y' = -k_2y^2$, $y(0) = q_e$, i.e. the $2A \to P$ equation with $k = k_2/2$.
The candidate $y = q_e/(1 + k_2q_et)$ is positive for $t \ge 0$, so the positive-solution uniqueness result applies;
inverting $q_t$ for $t > 0$ gives the linear form.

## Sources

- S. Gazvineh, M. Adeli and M. Nemati, "Metal-organic frameworks with linear and branched polyol backbones for dye removal", *Scientific Reports* (2026), [doi.org](https://doi.org/10.1038/s41598-026-37325-0), Eqn (4).
