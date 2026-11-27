# Reproduction number of a co-infection model as the maximum of submodel numbers

**Setting.** Two pathogens $P_1, P_2$ spread in one host population (possibly with a vector population for one of them). Infected compartments are partitioned into $Z_1$ (infected with $P_1$ only), $Z_2$ (infected with $P_2$ only), and $Z_{12}$ (co-infected, in any stage). Assume:

- at the disease-free equilibrium $x^0$ every uninfected compartment is free of both pathogens;
- a new $P_i$ infection of a disease-free host enters $Z_i$; entry into $Z_{12}$ requires a second infection of an already infected host, so its rate is at least quadratic in infected variables;
- the single-infection submodels (all variables of the other pathogen set to zero) have next-generation matrices $F_i V_i^{-1}$ with reproduction numbers $\mathcal{R}_i = \rho(F_i V_i^{-1})$.

**Theorem.** The next-generation matrix of the full model at $x^0$ has the form

$$FV^{-1} = \begin{pmatrix} F_1 V_1^{-1} & 0 & * \\ 0 & F_2 V_2^{-1} & * \\ 0 & 0 & 0 \end{pmatrix}$$

in the ordering $(Z_1, Z_2, Z_{12})$, hence the basic (or control) reproduction number of the co-infection model is

$$\mathcal{R}_0 = \max\{\mathcal{R}_1, \mathcal{R}_2\},$$

and by the van den Driessche–Watmough theorem the disease-free equilibrium is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$.

**Examples.**

1. *Dengue–COVID-19 with vectors:* $\mathcal{R}_0^{CD} = \max\{\mathcal{R}_0^{HC}, \mathcal{R}_0^{HD}\}$, where the dengue number is computed from the host–vector submodel.
2. *HIV/AIDS–pneumonia with pneumonia vaccination:* with recruitment $\Lambda$, natural death $d$, vaccinated fraction $\pi$ at entry, vaccine waning $\tau_1$, vaccine leakiness $\epsilon \in [0,1)$, pneumonia transmission $\beta_2$ (mass action), treatment $\kappa$ and disease death $d_P$,

$$\mathcal{R}_2 = \frac{\beta_2 \big(Y_1^0 + \epsilon Y_2^0\big)}{d + \kappa + d_P}, \qquad Y_1^0 = \frac{\Lambda(d + \tau_1 - \pi d)}{d(d+\tau_1)},\quad Y_2^0 = \frac{\Lambda \pi}{d + \tau_1},$$

and the threshold of the full model is $\mathcal{R}_3 = \max\{\mathcal{R}_1, \mathcal{R}_2\}$ with $\mathcal{R}_1$ the HIV/AIDS submodel number.
3. *COVID-19–influenza with vaccination against each pathogen* and *HBV–COVID-19:* the reproduction number of the full model is the larger of the two single-pathogen numbers, $\mathcal{R}_{HC} = \max\{\mathcal{R}_{CM}, \mathcal{R}_{HM}\}$ in the HBV–COVID-19 case.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [$R_0$ as a threshold for the linearized infected subsystem](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)

## Expansion

Linearizing at $x^0$ kills every term that requires two infected individuals of different types, so the new-infection Jacobian $F$ has no entries mapping into $Z_{12}$, and the transition matrix $V$ is block upper-triangular (co-infected hosts may leave $Z_{12}$ into single-infection or treatment compartments, but single infections do not become co-infections at linear order). Products and inverses of block-triangular matrices remain block-triangular, so the spectrum of $FV^{-1}$ is the union of the spectra of the diagonal blocks, which are exactly the submodel next-generation matrices, and the zero block from $Z_{12}$. The co-infected classes still matter for the endemic dynamics: their enhanced infectivity or susceptibility can make the bifurcation at $\mathcal{R}_0 = 1$ backward, which is tested with the [Castillo-Chavez–Song centre-manifold bifurcation theorem](../backward-bifurcation/castillo-chavez-song-centre-manifold-bifurcation-theorem.md); for example the COVID-19 submodel of an HBV–COVID-19 co-epidemic model can have a backward bifurcation, so even when $\max\{\mathcal{R}_1, \mathcal{R}_2\} < 1$ the reproduction numbers may need to be pushed below smaller critical values to guarantee elimination.

## Sources

- A. Omame, H. Rwezaura, M. L. Diagne, S. C. Inyama, J. M. Tchuenche, "COVID-19 and dengue co-infection in Brazil: optimal control and cost-effectiveness analysis", The European Physical Journal Plus 136 (2021) 1090, Sections 3–4 (Lemmas 3.2–3.3, equation (10), Theorem 4.1), <https://doi.org/10.1140/epjp/s13360-021-02030-6>.
- S. W. Teklu, K. P. Rao, "HIV/AIDS-Pneumonia Codynamics Model Analysis with Vaccination and Treatment", Computational and Mathematical Methods in Medicine 2022 (2022) 3105734, Sections 3.2 (pneumonia submodel, equations (9)–(12)) and 3.3.5 ($\mathcal{R}_3 = \max\{\mathcal{R}_1,\mathcal{R}_2\}$, Theorem 7), <https://doi.org/10.1155/2022/3105734>.
- M. M. Ojo, T. O. Benson, O. J. Peter, E. F. D. Goufo, "Nonlinear optimal control strategies for a mathematical model of COVID-19 and influenza co-infection", Physica A (2022), Section 3.3.1 (disease-free equilibrium, Eq. 29; reproduction number of the co-infection model, Eq. 30; Theorem 7), <https://doi.org/10.1016/j.physa.2022.128173> (PMC9461290).
- S. W. Teklu, "Impacts of optimal control strategies on the HBV and COVID-19 co-epidemic spreading dynamics", Scientific Reports (2024), effective reproduction number of the full co-epidemic model and backward bifurcation of the COVID-19 sub-model (Theorems 6–7), <https://doi.org/10.1038/s41598-024-55111-8> (PMC10912759).
