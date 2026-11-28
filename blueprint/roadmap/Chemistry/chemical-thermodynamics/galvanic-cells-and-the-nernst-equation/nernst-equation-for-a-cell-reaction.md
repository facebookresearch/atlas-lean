# Nernst equation for a cell reaction

For a cell without liquid junction, or with junction potential exactly zero, the equilibrium cell potential is $E_{\mathrm{cell,eq}}=E^\circ_{\mathrm{cell}}-\frac{RT}{zF}\ln Q_{\mathrm{rxn}}$; a nonzero junction potential $E_j$ adds $E_j$.

Let a galvanic cell at temperature $T>0$ have electron number $z>0$, cell reaction with stoichiometric
numbers $\nu_i$, full species activities $a_i>0$ (including any pressure factors) and [reaction quotient](../reaction-gibbs-energy-and-equilibrium-constants/reaction-quotient-and-equilibrium-constant.md)
$Q_{\mathrm{rxn}}=\prod_ia_i^{\nu_i}$, and let it satisfy the hypotheses of
[the cell reaction Gibbs energy and the equilibrium cell potential](cell-reaction-gibbs-energy-and-cell-potential.md).
If the cell has no liquid junction, or a junction whose potential is exactly $E_j=0$, then

$$E_{\mathrm{cell,eq}}=E^\circ_{\mathrm{cell}}-\frac{RT}{zF}\ln Q_{\mathrm{rxn}},$$

with $E^\circ_{\mathrm{cell}}$ the [standard cell potential](cell-reaction-and-its-electron-number.md). With a junction of
potential $E_j$ (and the separate electrode charge balances), $E_{\mathrm{cell,eq}}=E^\circ_{\mathrm{cell}}-\frac{RT}{zF}\ln Q_{\mathrm{rxn}}+E_j$,
so neglecting a small junction potential is an approximation with error exactly $E_j$.

Consequences in the exact case: $E_{\mathrm{cell,eq}}=E^\circ_{\mathrm{cell}}$ when every activity is one; with the other
activities held fixed, $E_{\mathrm{cell,eq}}$ increases when a product activity decreases or a reactant activity increases;
and $E_{\mathrm{cell,eq}}=0$ exactly when $Q_{\mathrm{rxn}}=K$, i.e. when the cell reaction has zero affinity. Rescaling the
reaction equation by $c>0$ multiplies $z$ and $\ln Q_{\mathrm{rxn}}$ by $c$ and leaves $E_{\mathrm{cell,eq}}$ unchanged.

## Context

Undergraduate electrochemistry. The same logarithmic law, applied to normalized ion concentrations across a membrane, is the [Nernst potential](../../../Biology/mathematical-neuroscience/nernst-potential-and-the-steady-state-cable-equa/nernst-potential.md); applied to a lattice of intercalation sites it gives the sloping open-circuit voltage of an intercalation electrode.

## Depends on

- [Cell reaction, electron number and cell potential](cell-reaction-and-its-electron-number.md)
- [Reaction quotient and thermodynamic equilibrium constant](../reaction-gibbs-energy-and-equilibrium-constants/reaction-quotient-and-equilibrium-constant.md)
- [Cell reaction Gibbs energy and the equilibrium cell potential](cell-reaction-gibbs-energy-and-cell-potential.md)

## Proof depends on

- [Standard cell potential and the equilibrium constant](standard-cell-potential-and-equilibrium-constant.md)
- [Reaction Gibbs energy from the reaction quotient](../reaction-gibbs-energy-and-equilibrium-constants/reaction-gibbs-energy-from-the-reaction-quotient.md)

## Expansion

With no junction, substitute $\Delta_rG=-zFE_{\mathrm{cell,eq}}$ and $\Delta_rG^\circ=-zFE^\circ_{\mathrm{cell}}$ into $\Delta_rG=\Delta_rG^\circ+RT\ln Q_{\mathrm{rxn}}$ and divide by $-zF$ (DeVoe Eq. 14.4.1). With a junction, $E_{\mathrm{cell,eq}}=-\Delta_rG/(zF)+E_j$ (Eq. 14.3.14) gives the extra $E_j$. With $\ln K=zFE^\circ/(RT)$, $E_{\mathrm{cell,eq}}=\frac{RT}{zF}\ln(K/Q_{\mathrm{rxn}})$ in the exact case. Rescaling is DeVoe's comparison of Eqs. 14.4.5 and 14.4.6.

## Sources

- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 14.4, Eqs. 14.4.1–14.4.6 and the discussion of rescaling the reaction equation. [Section 14.4](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/14%3A_Galvanic_Cells/14.04%3A_The_Nernst_Equation)
- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 14.3, Eq. 14.3.14 (cell with liquid junction). [Section 14.3](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/14%3A_Galvanic_Cells/14.03%3A_Molar_Reaction_Quantities_of_the_Cell_Reaction)
