# Theoretical specific capacity of an electrode material

The theoretical specific capacity of an electrode material whose formula unit (or repeat unit) of molar mass $M$ exchanges $n$ electrons is $nF/M$, which in battery units is $C_{\mathrm{th}}=nF/(3.6\,M)$ mAh g$^{-1}$ for $M$ in g mol$^{-1}$.

Let one formula unit (for a polymer, one repeat unit) of an electrode material have
[molar mass](../../amounts-and-stoichiometry/amount-of-substance-and-molar-mass/molar-mass.md) $M>0$ (g mol$^{-1}$), and suppose its complete electrode reaction transfers
$n>0$ electrons per formula unit, the [electron number](cell-reaction-and-its-electron-number.md) of the reaction
written per formula unit. The charge passed per unit mass when the reaction advances completely is
$nF/M$ (C g$^{-1}$); since $1\ \mathrm{mAh}=3.6$ C, the **theoretical specific capacity** is

$$C_{\mathrm{th}}=\frac{nF}{3.6\,M}\quad\mathrm{mAh\,g^{-1}} .$$

It is a stoichiometric upper bound for that reaction alone: it counts only the active material, assumes
every formula unit reacts with exactly $n$ electrons, and ignores additives, binders, electrolyte and
side reactions. Measured capacities can fall short of it, or exceed it when other charge-storage
processes contribute.

## Context

Undergraduate electrochemistry, used throughout battery research. For the layered organic cathode bis-tetraaminobenzoquinone (TAQ) of Chen, Banda, Wang, Oppenheim, Franceschi and Dincă, two two-electron redox couples per molecule give a reported theoretical specific capacity of 356 mAh g$^{-1}$, and an initial discharge capacity equal to it was measured with a vinylene-carbonate electrolyte additive; that measurement is experimental motivation, not part of the definition.

## Depends on

- [Cell reaction, electron number and cell potential](cell-reaction-and-its-electron-number.md)
- [Molar mass](../../amounts-and-stoichiometry/amount-of-substance-and-molar-mass/molar-mass.md)

## Proof depends on

None.

## Expansion

A definition. The value follows from the charge relation $dQ=-zF\,d\xi$ for advancement $\xi=m/M$ moles of formula units and the conversion $1\ \mathrm{mAh}=3.6\ \mathrm C$.

## Sources

- J. Zhang, X. Mu and Y. Mu, High-performance Li-organic batteries based on conjugated and nonconjugated Schiff-base polymer anode materials, *ACS Omega* 9 (2024), 12967–12975, Li-storage mechanism discussion, equation $C_{\mathrm{thro}}=nF/(3.6M)$. [doi:10.1021/acsomega.3c09299](https://doi.org/10.1021/acsomega.3c09299); PMC10956085
- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 14.1, Eq. 14.1.1 (charge per advancement). [Section 14.1](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/14%3A_Galvanic_Cells/14.01%3A_Cell_Diagrams_and_Cell_Reactions)
- T. Chen, H. Banda, J. Wang, J. J. Oppenheim, A. Franceschi and M. Dincă, A layered organic cathode for high-energy, fast-charging, and long-lasting Li-ion batteries, *ACS Central Science* 10 (2024), 569–578, introduction (theoretical specific capacity of 356 mAh g$^{-1}$ from two 2e$^-$ redox couples) and the electrolyte-optimization results. [doi:10.1021/acscentsci.3c01478](https://doi.org/10.1021/acscentsci.3c01478); PMC10979494
