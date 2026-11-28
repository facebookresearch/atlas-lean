# Two-state melting temperature of an oligonucleotide duplex

For two-state duplex formation with temperature-independent $\Delta H^\circ$ and $\Delta S^\circ$, the melting temperature is $T_M=\Delta H^\circ/(\Delta S^\circ+R\ln(C_{\mathrm{eff}}/c^\circ))$, with $C_{\mathrm{eff}}$ equal to the total strand concentration $C_T$ for a self-complementary duplex and $C_T/4$ for two complementary strands at equal concentration.

**Setting.** Duplex formation is two-state (only single strands and the full duplex are populated) in ideal dilute solution with standard concentration $c^\circ=1$ M. The standard enthalpy and entropy $\Delta H^\circ$, $\Delta S^\circ$ do not depend on temperature, $R$ is the gas constant in the same energy unit as $\Delta H^\circ$ (J or cal, not mixed), $T$ is in kelvin, and the dimensionless standard equilibrium constant satisfies $\Delta G^\circ=\Delta H^\circ-T\Delta S^\circ=-RT\ln K^\circ$.

- *Self-complementary:* $2A\rightleftharpoons A_2$, total strand concentration $C_T>0$ (counting strands, not duplexes), $K^\circ=c^\circ[A_2]/[A]^2$.
- *Non-self-complementary:* $A+B\rightleftharpoons AB$, $K^\circ=c^\circ[AB]/([A][B])$, strand totals $C_A\ge C_B>0$ and $C_T=C_A+C_B$.

Any symmetry contribution for self-complementary duplexes is included once, in $\Delta S^\circ$ (as in the [nearest-neighbor model](nearest-neighbor-model-of-duplex-stability.md)); no further symmetry factor enters the mass-action quotient.

**Statement.** Define the midpoint as the temperature at which half of all strands are in the duplex for a self-complementary duplex or for equal strand concentrations, and at which half of the limiting strand $B$ is in the duplex when $C_A>C_B$. At the midpoint $K^\circ=c^\circ/C_{\mathrm{eff}}$, and hence

$$T_M=\frac{\Delta H^\circ}{\Delta S^\circ+R\ln\!\left(C_{\mathrm{eff}}/c^\circ\right)},\qquad C_{\mathrm{eff}}=\begin{cases}C_T&\text{self-complementary},\\ C_T/4&\text{non-self-complementary},\ C_A=C_B,\\ C_A-C_B/2&\text{non-self-complementary},\ C_A>C_B,\end{cases}$$

whenever the denominator is nonzero and the quotient is positive. For a genuinely unimolecular two-state transition (for example a hairpin) the concentration term is absent and $T_M=\Delta H^\circ/\Delta S^\circ$, when $\Delta S^\circ\neq0$ and $\Delta H^\circ/\Delta S^\circ>0$. The source's remark that synthetic repeating polymers melt in a single, approximately two-state, concentration-independent transition with $T_M=\Delta H^\circ/\Delta S^\circ$ is an observation about those polymers, not a consequence of the bimolecular formula.

## Context

Undergraduate biochemistry. Because duplex formation is bimolecular, $T_M$ rises with strand concentration (for the usual $\Delta H^\circ<0$, $\Delta S^\circ<0$ on a branch where $T_M>0$); this is why melting temperatures must be quoted with concentrations. The Artzi RNA-triple-helix study reports apparent melting temperatures for single strands, duplexes and the triplex as stability evidence (Conde et al. 2016, Results and Fig. 2d); the triplex is a three-strand assembly not described by this duplex result.

## Depends on

- [Nearest-neighbor model of DNA duplex stability](nearest-neighbor-model-of-duplex-stability.md)

## Proof depends on

None.

## Expansion

Proof: at the defined midpoint the composition is fixed. Self-complementary: $[A]=C_T/2$, $[A_2]=C_T/4$, so $K^\circ=c^\circ/C_T$. Equal non-self-complementary strands: $[A]=[B]=[AB]=C_T/4$, so $K^\circ=4c^\circ/C_T$. Unequal strands: $[AB]=[B]=C_B/2$, $[A]=C_A-C_B/2$, so $K^\circ=c^\circ/(C_A-C_B/2)$. In each case $K^\circ=c^\circ/C_{\mathrm{eff}}$, and $\Delta H^\circ-T_M\Delta S^\circ=RT_M\ln(C_{\mathrm{eff}}/c^\circ)$ gives the formula. The nearest-neighbor page is linked only for the convention that the symmetry term sits in $\Delta S^\circ$; the formula holds for any $\Delta H^\circ,\Delta S^\circ$.

Remaining decomposition before the page can be marked ready: a definition page for ideal bimolecular two-state association with the standard-state convention (the analogue of the unimolecular two-state definition needed by the [two-state unfolding page](two-state-unfolding-and-the-van-t-hoff-slope.md)), and the mass balances at the midpoint as lemmas.

## Sources

- J. SantaLucia Jr., "A unified view of polymer, dumbbell, and oligonucleotide DNA nearest-neighbor thermodynamics", *Proceedings of the National Academy of Sciences USA* 95(4) (1998), 1460–1465, [doi.org](https://doi.org/10.1073/pnas.95.4.1460); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC19045/), section "Prediction of the Melting Temperature $T_M$", Eq. 3 (rendered as an image; the text defines $T_M$, gives the replacements $C_T/4$ and $C_A-C_B/2$, and the concentration-independent polymer observation $T_M=\Delta H^\circ/\Delta S^\circ$).
- J. Conde, N. Oliva, M. Atilano, H. S. Song and N. Artzi, "Self-assembled RNA-triple-helix hydrogel scaffold for microRNA modulation in the tumour microenvironment", *Nature Materials* 15(3) (2016), 353–363, [doi.org](https://doi.org/10.1038/nmat4497); author manuscript read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC6594154/), Results and Fig. 2d caption (context only).
