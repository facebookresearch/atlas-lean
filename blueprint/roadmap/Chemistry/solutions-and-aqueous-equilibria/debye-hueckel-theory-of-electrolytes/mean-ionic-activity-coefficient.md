# Mean ionic activity coefficient

For a strong electrolyte $\mathrm A_{\nu_+}\mathrm B_{\nu_-}$ the mean ionic activity coefficient is the geometric mean $\gamma_\pm=(\gamma_+^{\nu_+}\gamma_-^{\nu_-})^{1/\nu}$, $\nu=\nu_++\nu_-$, the measurable combination of single-ion coefficients.

Let a solute $\mathrm A_{\nu_+}\mathrm B_{\nu_-}$ dissociate completely into $\nu_+>0$ cations of charge
number $z_+>0$ and $\nu_->0$ anions of charge number $z_-<0$, with electroneutrality $\nu_+z_++\nu_-z_-=0$,
and let $\gamma_+,\gamma_->0$ be the single-ion molality-basis
[activity coefficients](../../chemical-thermodynamics/reaction-gibbs-energy-and-equilibrium-constants/chemical-potential-in-terms-of-relative-activity.md) at ion molalities $m_+,m_->0$. With $\nu=\nu_++\nu_-$ define

$$\gamma_\pm=\big(\gamma_+^{\nu_+}\gamma_-^{\nu_-}\big)^{1/\nu},\qquad m_\pm=\big(m_+^{\nu_+}m_-^{\nu_-}\big)^{1/\nu},\qquad a_\pm=\gamma_\pm\frac{m_\pm}{m^\circ}.$$

Equivalently $\ln\gamma_\pm=(\nu_+\ln\gamma_++\nu_-\ln\gamma_-)/\nu$. When this is the only electrolyte supplying
these ions, so that $m_+=\nu_+m_B$ and $m_-=\nu_-m_B$ for solute molality $m_B>0$,
$m_\pm=(\nu_+^{\nu_+}\nu_-^{\nu_-})^{1/\nu}m_B$; with a common ion from a second electrolyte the actual ion molalities must be
used. Individual $\gamma_+$ and $\gamma_-$ are not measurable; $\gamma_\pm$ is. At the standard pressure (pressure
factor one) the solute's chemical potential is $\mu_B=\mu_B^\circ+\nu RT\ln a_\pm$, that is, its activity is
$a_B=a_\pm^{\nu}$.

## Context

Undergraduate physical chemistry; $\gamma_\pm$ is what galvanic-cell measurements and Debye–Hückel theory both produce.

## Depends on

- [Chemical potential in terms of relative activity](../../chemical-thermodynamics/reaction-gibbs-energy-and-equilibrium-constants/chemical-potential-in-terms-of-relative-activity.md)

## Proof depends on

None.

## Expansion

A definition. The relation $\mu_B=\mu_B^\circ+\nu RT\ln a_\pm$ follows from $\mu_B=\nu_+\mu_++\nu_-\mu_-$ (DeVoe Eq. 10.3.3), whose electric-potential terms cancel by electroneutrality (Eq. 10.3.5), and the single-ion activity forms; DeVoe writes it as Eqs. 10.3.9–10.3.11 with the pressure factor.

## Sources

- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 10.3, Eqs. 10.3.3–10.3.11 and the multisolute example of Sec. 10.3.2. [Section 10.3](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/10%3A_Electrolyte_Solutions/10.03%3A_Electrolytes_in_General)
- E. R. Cohen, T. Cvitaš, J. G. Frey, B. Holmström, K. Kuchitsu, R. Marquardt, I. Mills, F. Pavese, M. Quack, J. Stohner, H. L. Strauss, M. Takami and A. J. Thor, *Quantities, Units and Symbols in Physical Chemistry* (IUPAC Green Book), 3rd edition, RSC Publishing, 2007, Section 2.13, p. 70 (mean ionic molality, mean ionic activity coefficient, mean ionic activity, notes 3–5). [doi:10.1039/9781847557889](https://doi.org/10.1039/9781847557889); [IUPAC PDF](https://iupac.org/wp-content/uploads/2019/05/IUPAC-GB3-2012-2ndPrinting-PDFsearchable.pdf)
