# Marcus cross relation

If the cross-reaction reorganization energy is the mean of the self-exchange ones, Marcus kinetics predicts the cross-reaction rate from the two self-exchange rates and the equilibrium constant: $k_{12}=(k_{11}k_{22}K_{12}f_{12})^{1/2}$ with $\ln f_{12}=(\ln K_{12})^2/(4\ln(k_{11}k_{22}/Z^2))$.

Model. Fix $T>0$ and use molar energies throughout (with per-molecule energies replace $RT$ by $k_BT$). Consider the
outer-sphere cross reaction $\mathrm A_1(\mathrm{ox})+\mathrm A_2(\mathrm{red})\to\mathrm A_1(\mathrm{red})+\mathrm A_2(\mathrm{ox})$ and the
self-exchange reactions of $\mathrm A_1$ and $\mathrm A_2$. Suppose each reaction $jk\in\{11,22,12\}$ has rate constant
$k_{jk}=Z\exp(-\Delta G^*_{jk}/RT)$ with one common prefactor $Z>0$ (same units as the $k_{jk}$; transmission
coefficient one), negligible work terms, and [Marcus barrier](marcus-activation-free-energy.md)
$\Delta G^*_{jk}=\frac{\lambda_{jk}}4(1+\Delta G^\circ_{jk}/\lambda_{jk})^2$ with $\lambda_{jk}>0$, where
$\Delta G^\circ_{11}=\Delta G^\circ_{22}=0$ and the [equilibrium constant](../../../chemical-thermodynamics/reaction-gibbs-energy-and-equilibrium-constants/reaction-quotient-and-equilibrium-constant.md)
of the cross reaction is $K_{12}=\exp(-\Delta G^\circ_{12}/RT)$. If

$$\lambda_{12}=\tfrac12(\lambda_{11}+\lambda_{22}),$$

then

$$k_{12}=\big(k_{11}k_{22}K_{12}f_{12}\big)^{1/2},\qquad \ln f_{12}=\frac{(\ln K_{12})^2}{4\ln\!\big(k_{11}k_{22}/Z^2\big)} .$$

Here $\ln(k_{11}k_{22}/Z^2)=-(\lambda_{11}+\lambda_{22})/(4RT)<0$, so $f_{12}\le1$, with $f_{12}=1$ exactly when $K_{12}=1$.
At fixed $\lambda_{11},\lambda_{22}$ and $T$, $\ln(k_{12}/Z)=\tfrac12\ln(k_{11}k_{22}/Z^2)+\tfrac12\ln K_{12}+O\big((\ln K_{12})^2\big)$.

## Context

Graduate inorganic and physical chemistry; one of the most widely tested predictions of Marcus theory, used to infer self-exchange rates of redox centres (including metalloprotein sites) from cross reactions with reagents of known parameters.

## Depends on

- [Marcus activation free energy](marcus-activation-free-energy.md)
- [Reaction quotient and thermodynamic equilibrium constant](../../../chemical-thermodynamics/reaction-gibbs-energy-and-equilibrium-constants/reaction-quotient-and-equilibrium-constant.md)

## Proof depends on

- [Standard reaction Gibbs energy and the equilibrium constant](../../../chemical-thermodynamics/reaction-gibbs-energy-and-equilibrium-constants/standard-reaction-gibbs-energy-and-equilibrium-constant.md)

## Expansion

From the barrier, $\Delta G^*_{jj}=\lambda_{jj}/4$, so $\lambda_{12}/4=\tfrac12(\Delta G^*_{11}+\Delta G^*_{22})$ and $\Delta G^*_{12}=\tfrac12(\Delta G^*_{11}+\Delta G^*_{22})+\tfrac12\Delta G^\circ_{12}+(\Delta G^\circ_{12})^2/(4\lambda_{12})$. Divide by $-RT$ and use $\ln(k_{jj}/Z)=-\Delta G^*_{jj}/RT$, $-\Delta G^\circ_{12}/RT=\ln K_{12}$ (the relation between the standard reaction Gibbs energy and $K$) and $\lambda_{12}=-2RT\ln(k_{11}k_{22}/Z^2)$ to get $\ln(k_{12}/Z)=\tfrac12\ln(k_{11}k_{22}K_{12}/Z^2)+(\ln K_{12})^2/(8\ln(k_{11}k_{22}/Z^2))$, which is Bertini's Eq. 6.26. The rendered intermediate Eqs. 6.25a–b of the edition read contain $\Delta G^*_{12}$ where $\Delta G^\circ_{12}$ is meant, and are not used.

## Sources

- I. Bertini, H. B. Gray, S. J. Lippard and J. S. Valentine, *Bioinorganic Chemistry*, University Science Books, 1994, Chemistry LibreTexts edition, Section 6.8 (Marcus Theory), Eqs. 6.17, 6.22–6.24 and the cross relation Eq. 6.26a–b (its prefactor $\nu_n$ written $Z$ here). [Section 6.8](https://chem.libretexts.org/Bookshelves/Inorganic_Chemistry/Book3A_Bioinorganic_Chemistry_%28Bertini_et_al.%29/06%3A_Electron_Transfer/6.08%3A_Marcus_Theory)
- R. A. Marcus, Electron transfer reactions in chemistry: theory and experiment, Nobel Lecture, 8 December 1992, p. 82, the cross relation, Eq. (10), from Eqs. (5) and (9). [Nobel Lecture PDF](https://www.nobelprize.org/uploads/2018/06/marcus-lecture.pdf)
