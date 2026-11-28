# Quantum yield of a photophysical process

The quantum yield of a process counts its events per photon absorbed by the system. It is the dimensionless efficiency against which emission, reaction and energy transfer are reported.

For monochromatic excitation at wavelength $\lambda$, the integral quantum yield over a measurement interval is

$$
\Phi(\lambda) = \frac{\text{number of events}}{\text{number of photons absorbed}} ,
$$

both counted on the same basis, as numbers of entities or as amounts of substance, and defined when the number of absorbed photons is positive; for a photochemical reaction the events are the amount of reactant consumed or product formed. The differential quantum yield is

$$
\Phi(\lambda) = \frac{\mathrm{d}x/\mathrm{d}t}{q^{0}_{n,\mathrm{p}}\big[1 - 10^{-A(\lambda)}\big]} ,
$$

where $\mathrm{d}x/\mathrm{d}t$ is the rate of change of the measured quantity, $q^{0}_{n,\mathrm{p}} > 0$ the incident photon flux on an amount basis and $A(\lambda) > 0$ the absorbance at the excitation wavelength, so that the bracket is the absorbed fraction and the denominator, the absorbed flux, is positive.

Both positivity conditions are required: the denominator of the differential form vanishes when the incident flux vanishes and when the absorbance does. The integral yield is the absorbed-flux-weighted average of the differential yield over the measurement, and the two coincide when the differential yield is constant; a constant absorbed flux alone does not make them equal. The yield is defined strictly for monochromatic excitation, and for polychromatic light an absorbed-flux average over the excitation band is quoted. The yields of a complete set of mutually exclusive decay channels of one excited state sum to $1$ *per excited state prepared*; per absorbed photon they sum to the yield with which that state is formed.

## Depends on

- [Beer–Lambert law](beer-lambert-law.md)

## Proof depends on

None.

## Expansion

A formal development takes an incident photon flux, an absorbance and an event-counting process, defines the integral and differential yields by the displays with the positivity hypotheses, and proves that the integral yield is the absorbed-flux-weighted mean of the differential yield, with equality under a constant differential yield. The channel-sum statement is the branching identity of this chapter and stays on its own page.

## Context

Undergraduate foundation. The efficiency measure for the emitters of this chapter: the photoluminescence quantum yield entering the emission cross-section and the delayed-fluorescence analysis is this quantity with emitted photons as the events.

## Sources

- Silvia E. Braslavsky, *Glossary of terms used in photochemistry, 3rd edition (IUPAC Recommendations 2006)*, Pure and Applied Chemistry 79 (2007) 293–465. DOI [10.1351/pac200779030293](https://doi.org/10.1351/pac200779030293), entry “quantum yield, $\Phi$”, pp. 406–407, with the integral and differential definitions and the note on monochromatic excitation.
