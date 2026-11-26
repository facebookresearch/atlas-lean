# Reproduction number of co-infection models

**Setting.** Two pathogens $1$ and $2$ (for example SARS-CoV-2 and influenza, or HBV and SARS-CoV-2) circulate in one host population. Compartments are classified as infected with pathogen $1$ only, pathogen $2$ only, or both (co-infected), plus uninfected classes (susceptible, vaccinated against either pathogen, recovered). Let $\mathcal R_1$ and $\mathcal R_2$ be the reproduction numbers of the single-pathogen sub-models (the system restricted to the invariant faces where the other pathogen is absent), computed by the next-generation method at the common disease-free equilibrium.

**Theorem.** If co-infected compartments are generated only through new infections of singly infected or co-infected hosts (so that at the disease-free equilibrium no new co-infections arise from a single infection), then the next-generation matrix of the full model at the disease-free equilibrium is block triangular with diagonal blocks the next-generation matrices of the two sub-models and a co-infection block with zero new-infection term, and

$$\mathcal R_0 = \rho(FV^{-1}) = \max\{\mathcal R_1, \mathcal R_2\}.$$

Hence the disease-free equilibrium of the co-infection model is locally asymptotically stable if $\max\{\mathcal R_1, \mathcal R_2\} < 1$ and unstable if it exceeds one; eliminating both diseases requires driving both single-pathogen reproduction numbers below one.

## Depends on

- [Basic reproduction number of the next-generation matrix](../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

At the disease-free equilibrium the forces of infection are linear in infectious densities, and becoming co-infected requires an already infected host to acquire the second pathogen, which is a product of two infected densities and therefore vanishes in the linearization. The new-infection matrix $F$ thus has no entries mapping into co-infected states, and the transition matrix $V$ is block triangular because co-infected hosts only leave by recovery or death into classes outside the single-infection blocks. The spectrum of a block-triangular matrix is the union of the spectra of its diagonal blocks, so the spectral radius of $FV^{-1}$ is the larger of the sub-model spectral radii. Endemic behaviour can be richer than this threshold suggests: each sub-model can have a backward bifurcation, so even when $\max\{\mathcal R_1, \mathcal R_2\} < 1$ the reproduction numbers may need to be pushed below smaller critical values to guarantee elimination.

## Sources

- M. M. Ojo, T. O. Benson, O. J. Peter, E. F. D. Goufo, "Nonlinear optimal control strategies for a mathematical model of COVID-19 and influenza co-infection", Physica A (2022), Section 3.3.1 (disease-free equilibrium, Eq. 29; reproduction number of the co-infection model, Eq. 30; Theorem 7). <https://doi.org/10.1016/j.physa.2022.128173> (PMC9461290).
- S. W. Teklu, "Impacts of optimal control strategies on the HBV and COVID-19 co-epidemic spreading dynamics", Scientific Reports (2024), effective reproduction number of the full co-epidemic model, $\mathcal R_{HC} = \max\{\mathcal R_{CM}, \mathcal R_{HM}\}$, and backward bifurcation of the COVID-19 sub-model (Theorems 6–7). <https://doi.org/10.1038/s41598-024-55111-8> (PMC10912759).
