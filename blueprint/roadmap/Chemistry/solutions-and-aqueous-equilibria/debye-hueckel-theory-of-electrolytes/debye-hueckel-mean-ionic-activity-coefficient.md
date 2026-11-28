# Debye–Hückel mean ionic activity coefficient

In the Debye–Hückel model, a strong electrolyte with ion charge numbers $z_+$, $z_-$ has $\ln\gamma_\pm=-A_{\mathrm{DH}}|z_+z_-|\sqrt{I_m}/(1+B_{\mathrm{DH}}a\sqrt{I_m})$, so $\gamma_\pm<1$ at positive ionic strength.

Let a strong electrolyte $\mathrm A_{\nu_+}\mathrm B_{\nu_-}$ satisfy electroneutrality $\nu_+z_++\nu_-z_-=0$
($z_+>0>z_-$), and suppose both ions follow the [Debye–Hückel activity coefficient model](debye-hueckel-activity-coefficient.md)
with the same closest-approach parameter $a$. Then its [mean ionic activity coefficient](mean-ionic-activity-coefficient.md)
satisfies

$$\ln\gamma_\pm=-\frac{A_{\mathrm{DH}}\,|z_+z_-|\,\sqrt{I_m}}{1+B_{\mathrm{DH}}a\sqrt{I_m}} .$$

Hence $\gamma_\pm<1$ whenever $I_m>0$ and $\gamma_\pm\to1$ as $I_m\to0$.

## Context

Graduate physical chemistry; this is the form compared with mean coefficients measured in galvanic cells.

## Depends on

- [Debye–Hückel activity coefficient model](debye-hueckel-activity-coefficient.md)
- [Mean ionic activity coefficient](mean-ionic-activity-coefficient.md)

## Proof depends on

None.

## Expansion

By definition $\ln\gamma_\pm=(\nu_+\ln\gamma_++\nu_-\ln\gamma_-)/\nu$, so the common factor $-A\sqrt{I}/(1+Ba\sqrt I)$ multiplies $(\nu_+z_+^2+\nu_-z_-^2)/\nu$. Electroneutrality gives $\nu_+z_+^2=-\nu_-z_-z_+$ and $\nu_-z_-^2=-\nu_+z_+z_-$, whose sum is $-z_+z_-\nu=|z_+z_-|\nu$ (DeVoe Eq. 10.4.7).

## Sources

- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 10.4, Eq. 10.4.7 (from Eqs. 10.3.8 and 10.4.1 with electroneutrality). [Section 10.4](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/10%3A_Electrolyte_Solutions/10.04%3A_The_Debye-Huckel_Theory)
