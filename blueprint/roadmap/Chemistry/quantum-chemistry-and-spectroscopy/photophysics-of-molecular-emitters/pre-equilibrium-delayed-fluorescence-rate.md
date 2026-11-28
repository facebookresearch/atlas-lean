# Pre-equilibrium rate constant of delayed fluorescence

Under fast singlet–triplet equilibration an emitter radiates from the singlet while most of its population sits in the triplet. The screening model multiplies the singlet's radiative rate constant by the equilibrium singlet fraction and reads the product as an estimated upper bound on the delayed-fluorescence rate.

Let the lowest excited singlet and triplet of an emitter be in thermal equilibrium at temperature $T > 0$ with gap $\Delta E_{\mathrm{ST}} = E(\mathrm{S}_1) - E(\mathrm{T}_1)$, and let $k_{\mathrm{f}} > 0$ be the supplied radiative rate constant of the singlet. Under the screening approximation of the source, in which non-radiative decay of both the singlet and the triplet is neglected and intersystem crossing from the singlet is assigned unit quantum yield, the delayed-fluorescence rate constant is modelled as

$$
k_{\mathrm{TADF}} = k_{\mathrm{f}} \cdot \frac{1}{1 + 3\exp\big(\Delta E_{\mathrm{ST}} / k_{\mathrm{B}} T\big)} .
$$

This is a stipulated approximation presented by its authors as an estimated upper bound, not an identity. Its assumptions do not form a consistent exact kinetic scheme: unit intersystem-crossing yield alongside a nonzero fluorescence rate cannot be a branching fraction of the same state, so the expression is a screening estimate whose accuracy the source discusses separately. The factor is the equilibrium singlet fraction of this chapter, so $k_{\mathrm{TADF}}$ increases as the gap shrinks and as $k_{\mathrm{f}}$ grows, and at $\Delta E_{\mathrm{ST}} = 0$ it is $k_{\mathrm{f}}/4$.

$k_{\mathrm{f}}$ is an input here. The source computes it from the oscillator strength of the singlet transition, the refractive index of the medium and the emission wavelength, through a radiative-rate relation of transition-strength type; that relation, with its conventions for degeneracy, lineshape and dielectric environment, is a prerequisite of any page that computes $k_{\mathrm{f}}$ rather than receiving it. In real emitters the two factors trade against each other, since separating the frontier orbitals shrinks the gap and lowers the oscillator strength; that trade-off is an observation about molecules, not a consequence of the display.

## Depends on

- [Singlet fraction of a thermally equilibrated singlet–triplet pair](boltzmann-singlet-fraction.md)
- [Lifetime of an excited state](excited-state-lifetime.md)

## Proof depends on

None.

## Expansion

A formal development takes $k_{\mathrm{f}} > 0$, a real gap and $T > 0$, and defines $k_{\mathrm{TADF}}$ as the product of $k_{\mathrm{f}}$ with the equilibrium singlet fraction, inheriting that factor's monotonicity and its value $1/4$ at zero gap. A development that also derives $k_{\mathrm{f}}$ needs the radiative-rate relation between absorption strength and spontaneous emission as a prerequisite; an empirical ranking of screened candidates is not part of the statement.

## Context

Research-level design model over graduate prerequisites. It is the quantity by which the high-throughput screen of Gómez-Bombarelli and co-workers ranked candidate emitters, and the quantitative content of the rule that a small singlet–triplet gap makes a good delayed-fluorescence emitter.

## Sources

- Rafael Gómez-Bombarelli, Jorge Aguilera-Iparraguirre, Timothy D. Hirzel, David Duvenaud, Dougal Maclaurin, Martin A. Blood-Forsythe, Hyun Sik Chae, Markus Einzinger, Dong-Gwang Ha, Tony Wu, Georgios Markopoulos, Soonok Jeon, Hosuk Kang, Hiroshi Miyazaki, Masaki Numata, Sunghan Kim, Wenliang Huang, Seong Ik Hong, Marc Baldo, Ryan P. Adams and Alán Aspuru-Guzik, *Design of efficient molecular organic light-emitting diodes by a high-throughput virtual screening and experimental approach*, Nature Materials 15 (2016) 1120–1127, main text p. 1122, Eq. 1 and the screening paragraph that states the neglected non-radiative channels and the unit intersystem-crossing yield. DOI [10.1038/nmat4717](https://doi.org/10.1038/nmat4717).
