# Standard transformed Gibbs energy of a pseudoisomer group

When the species of a biochemical reactant interconvert by binding hydrogen and magnesium ions and are in equilibrium at specified pH and pMg, the reactant behaves as one substance. Its standard transformed Gibbs energy is the Boltzmann-weighted free energy of its species, and the fractions of the species are fixed by the medium.

**Setting.** Fix $T>0$, $P$, $I$, pH and pMg, and use the [standard transformed Gibbs energies of formation of species](standard-transformed-gibbs-energy-of-a-species.md) $\Delta_fG_j'^\circ$ and $\Delta_fG_j'=\Delta_fG_j'^\circ+RT\ln[\mathrm B_j]$, with the magnesium terms of that page's derived extension when pMg is also specified (without them, read the hydrogen terms only and take the groups to differ only in hydrogen). A pseudoisomer group, or reactant, $i$ is a finite nonempty set $J_i$ of species whose formulas differ only in their numbers of hydrogen and magnesium atoms (for example $\mathrm{ATP^{4-}}$, $\mathrm{HATP^{3-}}$, $\mathrm{H_2ATP^{2-}}$, $\mathrm{MgATP^{2-}}$). Its species have concentrations $[\mathrm B_j]>0$, and the concentration of the reactant is $[\mathrm B_i]=\sum_{j\in J_i}[\mathrm B_j]$.

**Hypothesis (pseudoisomer equilibrium).** All species of the group have one common transformed Gibbs energy of formation, $\Delta_fG_j'=\Delta_fG_i'$ for $j\in J_i$. This is the equilibrium condition of the hydrogen- and magnesium-binding reactions inside the group, such as $\mathrm{HATP^{3-}}\rightleftharpoons\mathrm{ATP^{4-}}+\mathrm{H^+}$, with the free ions at the specified pH and pMg.

**Statement.** Then:

1. $\Delta_fG_i'=\Delta_fG_i'^\circ+RT\ln[\mathrm B_i]$, where

    $$
    \Delta_fG_i'^\circ=-RT\ln\sum_{j\in J_i}\exp\Bigl(-\frac{\Delta_fG_j'^\circ}{RT}\Bigr),
    $$

    the [Helmholtz free energy](../canonical-ensemble-of-a-finite-system/helmholtz-free-energy.md) of the finite system $J_i$ with energies $\Delta_fG_j'^\circ$ and inverse molar energy $\beta=1/(RT)$.

2. The equilibrium mole fractions within the group are

    $$
    r_j=\frac{[\mathrm B_j]}{[\mathrm B_i]}=\exp\Bigl(\frac{\Delta_fG_i'^\circ-\Delta_fG_j'^\circ}{RT}\Bigr),
    $$

    the [Boltzmann probabilities](../canonical-ensemble-of-a-finite-system/boltzmann-prob.md) of the finite system $J_i$ with energies $\Delta_fG_j'^\circ$ at inverse temperature $1/(RT)$. They are positive, sum to $1$, and depend on $T$, $I$, pH and pMg but not on $[\mathrm B_i]$.

3. Conversely, for every $[\mathrm B_i]>0$ the concentrations $[\mathrm B_j]=r_j[\mathrm B_i]$ satisfy the hypothesis, so the species distribution of a reactant at equilibrium is unique.

4. For each species $j\in J_i$, $\Delta_fG_i'^\circ=\Delta_fG_j'^\circ+RT\ln r_j$. The standard transformed energy of one species of the group, obtained by subtracting only that species' hydrogen and magnesium terms, is therefore not the reactant's standard transformed energy: it exceeds it by $-RT\ln r_j>0$ whenever the group has another species.

A group with one species has $\Delta_fG_i'^\circ=\Delta_fG_j'^\circ$ and $r_j=1$.

## Depends on

- [Standard transformed Gibbs energy of formation of a species](standard-transformed-gibbs-energy-of-a-species.md)
- [Helmholtz free energy from the partition function](../canonical-ensemble-of-a-finite-system/helmholtz-free-energy.md)
- [Boltzmann probability of a state](../canonical-ensemble-of-a-finite-system/boltzmann-prob.md)

## Proof depends on

- [Standard transformed Gibbs energy of formation of a species](standard-transformed-gibbs-energy-of-a-species.md)
- [Helmholtz free energy from the partition function](../canonical-ensemble-of-a-finite-system/helmholtz-free-energy.md)
- [Boltzmann probability of a state](../canonical-ensemble-of-a-finite-system/boltzmann-prob.md)

## Expansion

From $\Delta_fG_j'^\circ+RT\ln[\mathrm B_j]=\Delta_fG_i'$ we get $[\mathrm B_j]=\exp((\Delta_fG_i'-\Delta_fG_j'^\circ)/RT)$. Summing over $J_i$ gives $[\mathrm B_i]=\exp(\Delta_fG_i'/RT)\sum_j\exp(-\Delta_fG_j'^\circ/RT)$; taking logarithms gives part 1, and dividing gives part 2, a Boltzmann probability with partition function $\sum_j\exp(-\Delta_fG_j'^\circ/RT)>0$ because $J_i$ is nonempty. Part 3 reverses the computation, and part 4 is the logarithm of part 2. The sum over the group is where the aggregation lives: a reactant's energy is a log-sum over its species, not a shifted energy of one representative.

## Sources

- R. A. Alberty, A. Cornish-Bowden, R. N. Goldberg, G. G. Hammes, K. Tipton and H. V. Westerhoff, *Recommendations for terminology and databases for biochemical thermodynamics*, IUBMB Recommendations, Biophysical Chemistry 155 (2011) 89–103, <https://doi.org/10.1016/j.bpc.2011.03.007>. Equation numbers are those of the official IUBMB-hosted author manuscript (August 2010, 53 pages), <https://iubmb.qmul.ac.uk/thermod2/BiochemThermodynamics.pdf>: Section 2 for reactants as sums of species; Section 5, the statement after equation (5-4) that the species of a reactant share $\Delta_fG_j'$, and the relation $\Delta_fG_i'=\Delta_fG_i'^\circ+RT\ln[\mathrm B_i]$ after equation (5-5); Section 6, equations (6-6) and (6-8).
