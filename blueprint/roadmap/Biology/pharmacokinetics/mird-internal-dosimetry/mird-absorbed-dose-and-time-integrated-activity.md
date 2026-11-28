# MIRD absorbed dose and time-integrated activity

Absorbed dose is energy imparted per unit mass, $D = d\bar\varepsilon/dm$. For a radiopharmaceutical with activity $A(r_S, t)$ in source region $r_S$ at time $t$ after administration, the MIRD formalism writes the mean absorbed dose to a target region $r_T$ as

$$D(r_T) \;=\; \sum_{S} \tilde A(r_S)\, S(r_T \leftarrow r_S), \qquad \tilde A(r_S) \;=\; \int_0^\infty A(r_S, t)\, dt,$$

where $\tilde A(r_S)$, the time-integrated activity, is the total number of decays in $r_S$, and

$$S(r_T \leftarrow r_S) \;=\; \frac{\Delta\, \phi(r_T \leftarrow r_S)}{M(r_T)}$$

is the S value: $\Delta$ is the mean energy emitted per decay, $\phi(r_T \leftarrow r_S) \in [0,1]$ the fraction of energy emitted in $r_S$ that is absorbed in $r_T$, and $M(r_T)$ the target mass. If a fraction $f_S$ of the administered activity $A_0$ is taken up rapidly by $r_S$ and then cleared mono-exponentially, $A(r_S, t) = f_S A_0\, e^{-\lambda_e t}$ with effective rate $\lambda_e = \lambda_B + \lambda_P$ (biological clearance plus physical decay), then

$$\tilde A(r_S) \;=\; \frac{f_S A_0}{\lambda_e} \;=\; \frac{f_S A_0\, T_e}{\log 2}, \qquad \frac{1}{T_e} = \frac{1}{T_B} + \frac{1}{T_P},$$

so the effective half-life $T_e$ is shorter than both the biological half-life $T_B$ and the physical half-life $T_P$.

## Depends on

- [Half-life in terms of clearance and volume](../one-compartment-linear-pharmacokinetics/half-life-elim-rate.md)

## Expansion

The dose to $r_T$ from decays in $r_S$ is the number of decays times the energy each deposits in $r_T$, divided by the mass of $r_T$. That is $\tilde A\,\Delta\,\phi/M$, and contributions from different sources add. The integral of $f_SA_0e^{-\lambda_et}$ over $[0,\infty)$ is $f_SA_0/\lambda_e$; since $\lambda = \log 2/T$ for each process, $\lambda_e = \lambda_B + \lambda_P$ gives the harmonic relation for $T_e$. The factorization separates patient pharmacokinetics, measured by serial quantitative imaging to fit time–activity curves, from radionuclide physics and anatomy, which are tabulated for reference phantoms. For therapy, where tumour doses and patient-specific anatomy matter, voxel-level dosimetry replaces region-level S values with Monte Carlo or point-kernel calculations on PET/CT or SPECT/CT activity maps. Dose rate matters as well as total dose: the same $30$ Gy delivered over weeks at an exponentially decreasing rate has a very different effect from the same dose given in daily $2$-Gy radiotherapy fractions.

## Sources

- G. Sgouros, L. Bodei, M. R. McDevitt, J. R. Nedrow, "Radiopharmaceutical therapy in cancer: clinical advances and challenges", *Nature Reviews Drug Discovery* 19(9) (2020) 589–608, Box 1 (Equations 1–3) and Box 2, and section "Mechanism and biological effects", <https://doi.org/10.1038/s41573-020-0073-9> (PMC7390460).
