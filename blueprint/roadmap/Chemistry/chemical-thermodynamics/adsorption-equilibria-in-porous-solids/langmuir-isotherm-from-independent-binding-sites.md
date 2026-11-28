# Langmuir isotherm from independent binding sites

For $N_s$ independent sites in grand canonical equilibrium, the mean occupied fraction is $w/(1+w)$, $w = e^{\beta(\epsilon_a+\mu)}$; with a classical ideal-gas reservoir this is $P/(P+P_0)$.

Let a surface carry $N_s \ge 1$ distinguishable sites, each empty (energy $0$, occupancy $0$) or holding one molecule
(energy $-\epsilon_a$, occupancy $1$), with configurations $\sigma \in \{0,1\}^{N_s}$ of energy
$E(\sigma) = -\epsilon_a\sum_i\sigma_i$ and occupancy $N(\sigma) = \sum_i\sigma_i$. At absolute temperature $T > 0$
($\beta = 1/k_BT$, $k_B > 0$) and reservoir chemical potential $\mu$, measured from the same energy reference, give
$\sigma$ the weight $e^{-\beta(E(\sigma) - \mu N(\sigma))}$. Then the grand partition function is
$\Xi_s = (1 + w)^{N_s}$ with $w = e^{\beta(\epsilon_a + \mu)}$, and the mean occupied fraction is

$$
f_a = \frac{\langle N\rangle}{N_s} = \frac{w}{1 + w} .
$$

If the reservoir is a classical ideal gas at pressure $P > 0$ with chemical potential
$\mu = k_BT\ln(P\lambda^3/k_BT)$, $\lambda$ the thermal de Broglie wavelength and no internal partition factor (or one
absorbed into the energy reference), then

$$
f_a = \frac{P}{P+P_0}, \qquad P_0 = \frac{k_BT}{\lambda^3}\,e^{-\epsilon_a/k_BT},
$$

the Langmuir isotherm with affinity $b = 1/P_0$; $P_0$ is the pressure of half coverage.

## Context

Graduate level. This statistical-mechanical derivation identifies the Langmuir affinity with a binding energy, the usual microscopic reading of site-specific uptake in frameworks with open metal sites.

## Depends on

- [Langmuir isotherm](langmuir-isotherm.md)

## Proof depends on

- [Partition functions of independent subsystems multiply](../canonical-ensemble-of-a-finite-system/partition-function-combined-energy.md)

## Expansion

The factorization is the product rule for independent subsystems applied to the effective energies $E - \mu N$; the
weights then make the sites independent Bernoulli variables with success probability $w/(1+w)$, which gives $f_a$.
Missing prerequisites: the grand canonical weights and expectation on a finite configuration space with particle number
(the existing canonical pages have no chemical potential), and the classical ideal-gas chemical potential in the form
$k_BT\ln(P\lambda^3/k_BT)$ (the existing ideal-gas chemical potential is in entropy form, with a different
normalization).

## Sources

- Cersonsky Lab, *CBE 710 course notes* (University of Wisconsin–Madison, Fall 2023), Lecture 7, "Application of independent subsystems: the Langmuir isotherm", the single-site grand partition function $\xi_s = 1 + e^{\epsilon_a\beta}e^{\mu_a\beta}$ and the result $f_a = P/(P+P_0)$, [cersonsky-lab.github.io](https://cersonsky-lab.github.io/cbe710-notes-f2023/lecture_files/Lecture7.html).
