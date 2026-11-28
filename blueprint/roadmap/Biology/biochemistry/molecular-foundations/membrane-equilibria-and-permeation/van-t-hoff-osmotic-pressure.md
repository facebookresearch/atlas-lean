# Van 't Hoff osmotic pressure of dilute solutions

For a solution separated from pure solvent by a membrane permeable only to solvent, the equilibrium osmotic pressure obeys the van 't Hoff limiting law $\Pi/(cRT)\to1$ as the solute particle concentration $c\to0^+$; with mass concentration $C$ this gives the molar mass as the $C\to0$ limit of $RTC/\Pi$.

**Setting.** A solution and pure solvent at the same temperature $T>0$ are separated by a semipermeable membrane that passes solvent but retains every solute species (no leakage). At equilibrium the solution side is at a higher pressure by the osmotic pressure $\Pi$ (for example a hydrostatic head $\Pi=\rho gh$). Solute particles are counted as they exist in solution (association or ion dissociation changes the count and is excluded unless accounted for).

**Statement.**

1. *Ideal-solution relation.* If the solvent behaves ideally (chemical potential $\mu_A=\mu_A^\circ+RT\ln x_A$ with solvent mole fraction $x_A$) and its molar volume $\bar V_A$ is independent of pressure, then exactly

$$\Pi\,\bar V_A=-RT\ln x_A .$$

2. *Van 't Hoff limiting law.* Under the assumptions of item 1, with a regular dilute limit of the solvent molar volume, as the solute particle concentration $c$ (moles of solute particles per unit volume) tends to zero,

$$\frac{\Pi}{cRT}\to1,\qquad\text{so}\qquad \Pi=cRT\ \text{to first order in }c.$$

For a single solute of molar mass $M$ at mass concentration $C$, $c=C/M$, and $1/M=\lim_{C\to0^+}\Pi/(RTC)$. For a fixed-composition mixture of retained species with mass concentrations $C_i$, the same limit gives the number-average molar mass $M_n=\sum_iC_i\big/\sum_i(C_i/M_i)$.

3. *Osmotic virial expansion.* For solutions modelled by an osmotic virial expansion, the reduced osmotic pressure is written as

$$\frac{\Pi}{RTC}=\frac{1}{M}\left(1+B_2'C+B_3'C^2+\cdots\right),$$

where $B_2'$ has units of reciprocal mass concentration and $B_3'$ of its square; the coefficients are empirical properties of a given solute–solvent pair.

## Context

Undergraduate physical chemistry for the life sciences. Osmometry is a classical method for macromolecular molar mass, and osmotic pressure differences drive water flux across membranes, as in the [reverse-osmosis flux law](../../../../Physics/fluid-mechanics/filtration-and-sedimentation/membrane-flux-with-a-reflection-coefficient.md). Osmotic swelling is a general design consideration for hydrogels of the kind the Artzi laboratory builds (Wyss Institute profile), but no Artzi result is derived here; hydrogel transport is outside this foundations page.

## Depends on

None.

## Proof depends on

- [Chemical potential from the entropy](../../../../Chemistry/chemical-thermodynamics/fundamental-relation-of-thermodynamics/chem-pot.md)

## Expansion

Proof route (as in the source's derivation): equilibrium of solvent across the membrane requires $\mu_A^\circ(p)=\mu_A(x_A,p+\Pi)$; with $\mu_A=\mu_A^\circ+RT\ln x_A$ and $(\partial\mu_A/\partial p)_T=\bar V_A$ constant this gives item 1. For item 2, $-\ln x_A=x_B+O(x_B^2)$ with $x_B$ the total solute mole fraction, and $x_B/\bar V_A=c\,(1+O(c))$ in the dilute limit. The number average follows because each retained particle contributes independently to $c$ at leading order. The source writes two intermediate integrals with shorthand limits ($\int_p^{\Pi}$) before giving the correct $\int_p^{p+\Pi}\bar V\,dp=\bar V\Pi$.

Remaining decomposition before the page can be marked ready: (i) a page for the ideal-solution chemical potential of the solvent (the linked page gives chemical potential from entropy, not the mixing form); (ii) a lemma for the pressure derivative $(\partial\mu/\partial p)_T=\bar V$; (iii) the asymptotic estimates in item 2 written with explicit error terms.

## Sources

- J. Gutow, *Chem 370: Physical Chemistry 1 – Thermodynamics*, LibreTexts (University of Wisconsin Oshkosh), Section 1.8 "Colligative Properties", subsections "Osmotic Pressure and Osmotic Virial Coefficients" (Eqs. 1.8.13–1.8.17: $\Pi=\rho gh$, $\Pi=cRT$, $\Pi/(RTC)=1/M_w$ and the virial expansion) and "Derivation of osmotic pressure equation form" (the chemical-potential derivation ending in $x_BRT=\bar V\Pi$) (read at [chem.libretexts.org](https://chem.libretexts.org/Courses/University_of_Wisconsin_Oshkosh/Chem_370%3A_Physical_Chemistry_1_-_Thermodynamics_%28Gutow%29/01%3A_Thermodynamics/1.08%3A_Colligative_Properties)).
- Wyss Institute faculty profile of Natalie Artzi, [wyss.harvard.edu](https://wyss.harvard.edu/team/core-faculty/natalie-artzi-ph-d/) (context sentence only).
