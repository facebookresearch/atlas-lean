# Ionic strength

The ionic strength of an electrolyte solution is $I_m=\tfrac12\sum_im_iz_i^2$ on the molality basis, or $I_c=\tfrac12\sum_ic_iz_i^2$ on the concentration basis, summed over all ion species.

Let a solution contain ion species $i$ with charge numbers $z_i\in\mathbb Z\setminus\{0\}$, molalities
$m_i\ge0$ ([molality](../concentration-units-of-solutions/molality.md), mol kg$^{-1}$) and amount concentrations $c_i\ge0$
([molarity](../concentration-units-of-solutions/molarity.md), mol m$^{-3}$ or mol dm$^{-3}$). The **ionic strength** is

$$I_m=\frac12\sum_i m_iz_i^2\quad\text{(molality basis)},\qquad I_c=\frac12\sum_i c_iz_i^2\quad\text{(concentration basis)} .$$

Uncharged species do not contribute. For a single strong electrolyte $\mathrm A_{\nu_+}\mathrm B_{\nu_-}$ of
molality $m$, $m_+=\nu_+m$ and $m_-=\nu_-m$, so $I_m=\tfrac12m(\nu_+z_+^2+\nu_-z_-^2)$; for a uni-univalent electrolyte ($z_+=1$, $z_-=-1$,
$\nu_\pm=1$) $I_m=m$, while a $z{:}z$ electrolyte with $z=2$ gives $I_m=4m$. In a dilute solution of a solvent of density $\rho_A^*$, $c_i\approx\rho_A^*m_i$ and
$I_c\approx\rho_A^*I_m$.

## Context

Undergraduate physical chemistry. Lewis and Randall introduced the ionic strength empirically; the Debye–Hückel theory explains why dilute-solution activity coefficients depend on composition only through it.

## Depends on

- [Molality](../concentration-units-of-solutions/molality.md)
- [Molarity](../concentration-units-of-solutions/molarity.md)

## Proof depends on

None.

## Expansion

A definition. The single-electrolyte formula substitutes $m_\pm=\nu_\pm m$; the dilute-solution relation between the two bases is DeVoe's step at the end of Sec. 10.5.

## Sources

- E. R. Cohen, T. Cvitaš, J. G. Frey, B. Holmström, K. Kuchitsu, R. Marquardt, I. Mills, F. Pavese, M. Quack, J. Stohner, H. L. Strauss, M. Takami and A. J. Thor, *Quantities, Units and Symbols in Physical Chemistry* (IUPAC Green Book), 3rd edition, RSC Publishing, 2007, Section 2.13, p. 70 (ionic strength, molality basis $I_m=\frac12\sum_im_iz_i^2$ and concentration basis $I_c=\frac12\sum_ic_iz_i^2$, note 2). [doi:10.1039/9781847557889](https://doi.org/10.1039/9781847557889); [IUPAC PDF](https://iupac.org/wp-content/uploads/2019/05/IUPAC-GB3-2012-2ndPrinting-PDFsearchable.pdf)
- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 10.5, definition of $I_c$ after Eq. 10.5.2 and the relation $I_c=\rho_A^*I_m$ in dilute solution. [Section 10.5](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/10%3A_Electrolyte_Solutions/10.05%3A_Derivation_of_the_Debye-Huckel_Theory)
