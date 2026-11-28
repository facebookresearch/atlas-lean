# Stern–Volmer relation for dynamic quenching

A dynamic quencher adds one first-order decay channel whose rate constant is proportional to the quencher concentration. Emission yield and lifetime then fall by the same factor, linear in that concentration.

Let an excited state decay, without quencher, by first-order channels of positive total rate constant $1/\tau^{0}$, with radiative rate constant $k_{\mathrm{r}} > 0$, and let the yield per prepared excited state be $\Phi_{0} = k_{\mathrm{r}}\tau^{0} > 0$. Let a quencher $\mathrm{Q}$ at constant concentration $[\mathrm{Q}] \ge 0$ add a bimolecular channel of rate constant $k_{\mathrm{q}} \ge 0$, leaving the other rate constants and the preparation of the state unchanged. Then

$$
\frac{\Phi_{0}}{\Phi} = 1 + k_{\mathrm{q}} \tau^{0} [\mathrm{Q}] ,
\qquad
\frac{\tau^{0}}{\tau} = 1 + k_{\mathrm{q}} \tau^{0} [\mathrm{Q}] ,
$$

with $\Phi, \tau$ the yield and lifetime in the presence of the quencher, and the slope against $[\mathrm{Q}]$ is the Stern–Volmer constant $K_{\mathrm{SV}} = k_{\mathrm{q}}\tau^{0}$. Yields per absorbed photon obey the same ratio when the two measurements share one and the same *positive* yield of forming the excited state, since that common positive factor cancels; a vanishing formation yield makes both photon-based yields zero and the ratio undefined. Emission intensities $M_{0}, M$ may replace the yields when excitation, absorption and detection are the same in both measurements.

Here $\tau^{0}$ is the unquenched *total* lifetime, which the source distinguishes from the radiative lifetime; they agree only for a purely radiative decay. The hypotheses are what make the relation testable: quenching is dynamic, that is a bimolecular reaction of the excited state, so it shortens the lifetime; the quencher concentration is constant during the measurement; the unquenched decay is first order; and one mechanism operates.

Static quenching, in which ground-state molecules are removed by complexation, is a different ideal model with a different observable. Under comparable excitation and detection the measured intensity is proportional to the free emissive population, so for a $1{:}1$ dark complex the intensity ratio is linear in the concentration of *free* quencher, $M_{0}/M = 1 + K[\mathrm{Q}]_{\mathrm{free}}$, while the lifetime of that uncomplexed population is unchanged. Plotted against total added quencher the same model curves whenever a non-negligible fraction is bound, so curvature against the experimental control shows that a model's assumptions fail and is not by itself mechanistic evidence; what separates these two ideal models is the flat lifetime plot of the static one.

## Depends on

- [Lifetime of an excited state](excited-state-lifetime.md)
- [Quantum yield of a photophysical process](quantum-yield-of-a-photophysical-process.md)

## Proof depends on

- [Branching of competing first-order decay channels](branching-of-competing-decay-channels.md)

## Expansion

With the quencher present the total rate constant is $1/\tau^{0} + k_{\mathrm{q}}[\mathrm{Q}]$, so $\tau = (1/\tau^{0} + k_{\mathrm{q}}[\mathrm{Q}])^{-1}$ and the lifetime ratio is immediate. The branching identity gives the per-prepared-state yields $\Phi = k_{\mathrm{r}}\tau$ and $\Phi_{0} = k_{\mathrm{r}}\tau^{0}$ with the same $k_{\mathrm{r}} > 0$, so dividing cancels it and the yield ratio equals the lifetime ratio; positivity of $k_{\mathrm{r}}$ and of $\Phi$ is what makes the division legitimate, and one common positive formation yield is what carries the identity to yields per absorbed photon.

## Context

Undergraduate to graduate. The standard analysis for oxygen quenching and triplet diagnostics, used throughout the emitter characterisation this chapter draws on, and the reason degassed samples are required when delayed emission is measured.

## Sources

- Silvia E. Braslavsky, *Glossary of terms used in photochemistry, 3rd edition (IUPAC Recommendations 2006)*, Pure and Applied Chemistry 79 (2007) 293–465. DOI [10.1351/pac200779030293](https://doi.org/10.1351/pac200779030293), entry “Stern–Volmer kinetic relationships”, pp. 429–430, Eqs. 1, 2 and 4, with the notes on dynamic quenching and on $K_{\mathrm{SV}} = k_{\mathrm{q}}\tau^{0}$.
