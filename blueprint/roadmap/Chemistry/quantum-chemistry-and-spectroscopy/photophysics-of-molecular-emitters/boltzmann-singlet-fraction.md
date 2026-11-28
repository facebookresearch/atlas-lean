# Singlet fraction of a thermally equilibrated singlet–triplet pair

When the lowest excited singlet and triplet of a molecule are in thermal equilibrium, the share of the excited population in the emitting singlet is fixed by the singlet–triplet gap and the threefold degeneracy of the triplet. A small gap keeps that share usable at room temperature.

Let the lowest excited singlet $\mathrm{S}_1$, non-degenerate, and the lowest excited triplet $\mathrm{T}_1$, with three degenerate sublevels, be in thermal equilibrium at temperature $T > 0$, with gap

$$
\Delta E_{\mathrm{ST}} = E(\mathrm{S}_1) - E(\mathrm{T}_1) .
$$

Conditional on the molecule occupying this two-state manifold, the fraction in the singlet is

$$
x_{\mathrm{S}} = \frac{1}{1 + 3\exp\big(\Delta E_{\mathrm{ST}} / k_{\mathrm{B}} T\big)} .
$$

The denominator exceeds one, so the expression is defined for every real gap and every $T > 0$. It decreases strictly in $\Delta E_{\mathrm{ST}}$ and, for $\Delta E_{\mathrm{ST}} > 0$, increases strictly in $T$. A degenerate pair, $\Delta E_{\mathrm{ST}} = 0$, gives $x_{\mathrm{S}} = 1/4$, the share of one sublevel among four; a large positive gap gives $x_{\mathrm{S}} \to 0$. The inverted case $\Delta E_{\mathrm{ST}} < 0$ with $|\Delta E_{\mathrm{ST}}| \gg k_{\mathrm{B}}T$ gives $x_{\mathrm{S}} \to 1$ by the same algebra; it lies outside the positive-gap regime the source screens and is recorded as an extension, not as a result of that work.

Two readings must be kept apart. The identity above is an equilibrium statement about populations, conditional on the $\mathrm{S}_1/\mathrm{T}_1$ manifold, so other states need not be unpopulated, only excluded from the conditioning. Whether equilibrium is reached is a kinetic question: it requires exchange between the two states to be fast compared with their decay, which is the assumption the delayed-fluorescence model of this chapter adds. Nothing here involves a radiative rate constant.

## Depends on

None.

## Proof depends on

- [Boltzmann probability of a state](../../chemical-thermodynamics/canonical-ensemble-of-a-finite-system/boltzmann-prob.md)

## Expansion

Apply the Boltzmann distribution to the four sublevels of the manifold, one singlet and three degenerate triplet sublevels: populations are proportional to $\exp(-E/k_{\mathrm{B}}T)$, so taking $E(\mathrm{T}_1)$ as the zero of energy gives $x_{\mathrm{S}} = \exp(-\Delta E_{\mathrm{ST}}/k_{\mathrm{B}}T)/\big(\exp(-\Delta E_{\mathrm{ST}}/k_{\mathrm{B}}T) + 3\big)$, which is the display after multiplying through by $\exp(\Delta E_{\mathrm{ST}}/k_{\mathrm{B}}T)$. Monotonicity in each argument is differentiation, and the endpoint values are limits. The identity is a consequence of the linked distribution rather than an independent experimental result.

## Context

Graduate. The statistical factor in the design of thermally activated delayed-fluorescence emitters: Gómez-Bombarelli and co-workers use exactly this weight when screening candidates, which is why the singlet–triplet gap is the screened quantity.

## Sources

- Rafael Gómez-Bombarelli, Jorge Aguilera-Iparraguirre, Timothy D. Hirzel, David Duvenaud, Dougal Maclaurin, Martin A. Blood-Forsythe, Hyun Sik Chae, Markus Einzinger, Dong-Gwang Ha, Tony Wu, Georgios Markopoulos, Soonok Jeon, Hosuk Kang, Hiroshi Miyazaki, Masaki Numata, Sunghan Kim, Wenliang Huang, Seong Ik Hong, Marc Baldo, Ryan P. Adams and Alán Aspuru-Guzik, *Design of efficient molecular organic light-emitting diodes by a high-throughput virtual screening and experimental approach*, Nature Materials 15 (2016) 1120–1127, main text p. 1122, Eq. 1 and the pre-equilibrium paragraph, which weights the singlet by the ratio of triplet to singlet states. DOI [10.1038/nmat4717](https://doi.org/10.1038/nmat4717).
