# Lifetime of an excited state

An excited state decaying by first-order processes has a lifetime equal to the reciprocal of the sum of the rate constants of its channels: the time in which a population prepared in that state falls to $1/e$ of its initial value.

Let an excited molecular entity decay by first-order processes with rate constants $k_i \ge 0$, $i = 1, \dots, m$, whose sum is positive, so that a population prepared with $c(0) > 0$ obeys $\dot{c} = -\big(\sum_i k_i\big)c$. Its lifetime is

$$
\tau = \frac{1}{\sum_{i} k_{i}} ,
$$

and then $c(\tau) = c(0)/e$ and the half-life is $\tau_{1/2} = \tau \ln 2$. The SI unit is the second.

If the radiative channels have rate constants summing to $k_{\mathrm{r}} > 0$, the *radiative lifetime* is $\tau_{0} = 1/k_{\mathrm{r}}$, the lifetime the state would have if those were its only channels; then $\tau \le \tau_{0}$, with equality exactly when every non-radiative rate constant is zero. With no radiative channel, or with all radiative rate constants zero, $\tau_{0}$ is not finite and the comparison is empty.

The positivity of $\sum_i k_i$ is needed: a state with no decay channel has no lifetime. The definition is tied to first-order kinetics; for a decay that is not first order the measured quantity depends on the initial concentration or on a quencher concentration, and only an initial or mean decay time can be quoted, which is why the source reserves the word lifetime for the first-order case.

## Depends on

None.

## Proof depends on

- [Integrated first-order rate law](../../chemical-kinetics/rate-laws/first-order-sol.md)
- [Half-life of a first-order reaction](../../chemical-kinetics/rate-laws/first-order-sol-half-life.md)

## Expansion

A formal development defines $\tau$ by the display for a finite family of nonnegative rate constants with positive sum, then derives $c(\tau) = c(0)/e$ from the integrated first-order law $c(t) = c(0)\exp(-t/\tau)$ with $c(0) > 0$, which is why that law is a proof prerequisite rather than part of the statement. The half-life identity is the linked first-order half-life statement with $k = 1/\tau$. The inequality $\tau \le \tau_{0}$ is monotonicity of $x \mapsto 1/x$ on the positive reals applied to $k_{\mathrm{r}} \le \sum_i k_i$, and the equality case is the vanishing of the remaining rate constants.

## Context

Undergraduate foundation. Every photophysical observable of this chapter, from quantum yields to energy-transfer efficiencies and emission cross-sections, is quoted against this lifetime.

## Sources

- Silvia E. Braslavsky, *Glossary of terms used in photochemistry, 3rd edition (IUPAC Recommendations 2006)*, Pure and Applied Chemistry 79 (2007) 293–465. DOI [10.1351/pac200779030293](https://doi.org/10.1351/pac200779030293), entry “lifetime, s”, p. 363, with its mathematical definition and its notes on non-first-order decay and on half-life, and the entry “radiative lifetime, s”, p. 411, which takes the sum over radiative steps when there is more than one.
