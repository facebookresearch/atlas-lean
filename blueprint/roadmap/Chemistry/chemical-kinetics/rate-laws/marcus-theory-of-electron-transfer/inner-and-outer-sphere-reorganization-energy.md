# Inner- and outer-sphere reorganization energy

The Marcus reorganization energy is modelled as an inner-sphere part from bond-length changes, $\lambda_i=\tfrac12\sum_jk_j(\Delta x_j)^2$, plus an outer-sphere part from solvent repolarization, $\lambda_o=e^2\big(\frac1{2r_A}+\frac1{2r_B}-\frac1d\big)\big(\frac1{D_{op}}-\frac1{D_s}\big)$ for two spheres in a dielectric continuum.

In Marcus theory the [reorganization energy](marcus-two-parabola-model.md) is modelled as $\lambda=\lambda_i+\lambda_o$ with

$$\lambda_i=\frac12\sum_jk_j(\Delta x_j)^2,\qquad
\lambda_o=e^2\Big(\frac1{2r_A}+\frac1{2r_B}-\frac1d\Big)\Big(\frac1{D_{op}}-\frac1{D_s}\Big),$$

where $k_j>0$ are normal-mode force constants and $\Delta x_j$ the differences of equilibrium values of the
corresponding mode coordinates between the oxidized and reduced forms of the redox centres; $r_A,r_B>0$ are the
reactant radii, $d>0$ the centre-to-centre distance in the activated complex (usually $d=r_A+r_B$), $D_{op}>0$ the
optical dielectric constant (square of the refractive index) and $D_s>0$ the static dielectric constant of the
medium. The $\lambda_o$ formula is for one transferred electron in Gaussian units; in SI units $e^2$ is replaced by
$e^2/(4\pi\varepsilon_0)$. For $d\ge r_A+r_B$ the first factor is positive, so $\lambda_o>0$ exactly when $D_s>D_{op}$.
Within the formula, for $D_s>D_{op}$: $\lambda_o$ increases with the separation $d$ at fixed radii (the first factor
has derivative $1/d^2$), decreases when both radii are multiplied by a common factor $s>1$ at contact ($d=r_A+r_B$), and decreases as the dielectric
contrast $1/D_{op}-1/D_s$ decreases. The outer-sphere formula assumes spherical reactants and a dielectric continuum
solvent.

## Context

Graduate inorganic and physical chemistry. The reorganization energy is the input $\lambda$ of the Marcus activation free energy $(\Delta G^\circ+\lambda)^2/(4\lambda)$; how the barrier responds to a change of $\lambda$ depends on $\Delta G^\circ$.

## Depends on

- [Marcus two-parabola model and the reorganization energy](marcus-two-parabola-model.md)

## Proof depends on

None.

## Expansion

A model definition. Positivity: $\frac1{2r_A}+\frac1{2r_B}\ge\frac2{r_A+r_B}>\frac1{r_A+r_B}\ge\frac1d$ for $d\ge r_A+r_B$. At contact the first factor is $(r_A^2+r_B^2)/(2r_Ar_B(r_A+r_B))$, homogeneous of degree $-1$ in the radii. The continuum formula comes from the nonequilibrium polarization free energy of two spheres in Marcus's 1956 treatment.

## Sources

- I. Bertini, H. B. Gray, S. J. Lippard and J. S. Valentine, *Bioinorganic Chemistry*, University Science Books, 1994, Chemistry LibreTexts edition, Section 6.8 (Marcus Theory), Eqs. 6.19–6.20 and the following discussion. [Section 6.8](https://chem.libretexts.org/Bookshelves/Inorganic_Chemistry/Book3A_Bioinorganic_Chemistry_%28Bertini_et_al.%29/06%3A_Electron_Transfer/6.08%3A_Marcus_Theory)
- R. A. Marcus, Electron transfer reactions in chemistry: theory and experiment, Nobel Lecture, 8 December 1992, p. 79, two-sphere model of the solvent reorganization term (Eq. (7)) and the vibrational term (Eq. (8)). [Nobel Lecture PDF](https://www.nobelprize.org/uploads/2018/06/marcus-lecture.pdf)
