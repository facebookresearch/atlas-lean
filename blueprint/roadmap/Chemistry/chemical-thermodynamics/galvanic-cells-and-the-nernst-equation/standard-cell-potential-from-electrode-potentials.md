# Standard cell potential from standard electrode potentials

The standard cell potential of any cell is the standard electrode potential of its right electrode minus that of its left electrode, $E^\circ_{\mathrm{cell}}=E^\circ_{\mathrm R}-E^\circ_{\mathrm L}$.

Let a cell have left electrode L and right electrode R with standard electrode potentials $E^\circ_{\mathrm L}$
and $E^\circ_{\mathrm R}$ (each measured against the standard hydrogen electrode), at the same temperature and
with the same standard states. Then its standard cell potential is

$$E^\circ_{\mathrm{cell}}=E^\circ_{\mathrm R}-E^\circ_{\mathrm L},$$

independently of how the cell reaction is scaled. Hence standard potentials of $n$ electrodes measured
in $n$ cells determine those of all $\binom n2$ cells built from them (one orientation per pair; the reverse cell has the opposite sign), and no cell needs to contain an actual
hydrogen electrode except to fix the reference.

## Context

Undergraduate electrochemistry. Combined with the Nernst equation it gives the open-circuit voltage of a full cell from half-cell data.

## Depends on

- [Standard electrode potential](standard-electrode-potential.md)
- [Cell reaction, electron number and cell potential](cell-reaction-and-its-electron-number.md)

## Proof depends on

- [Standard cell potential and the equilibrium constant](standard-cell-potential-and-equilibrium-constant.md)
- [Molar reaction Gibbs energy and its standard value](../reaction-gibbs-energy-and-equilibrium-constants/molar-reaction-gibbs-energy.md)

## Expansion

Write the cells H|L and H|R (hydrogen electrode on the left) with the same electron number $z$ as the cell L|R: the cell reaction of H|L plus that of L|R equals that of H|R (DeVoe Eq. 14.6.1). Standard molar reaction Gibbs energies add because $\Delta_rG^\circ=\sum\nu_i\mu_i^\circ$ is linear in $\nu$, and each equals $-zF$ times its standard cell potential; dividing by $-zF$ gives $E^\circ_{\mathrm{cell}}+E^\circ_{\mathrm L}=E^\circ_{\mathrm R}$ (DeVoe Eqs. 14.6.2–14.6.3).

## Sources

- H. DeVoe, *Thermodynamics and Chemistry*, 2nd edition, Chemistry LibreTexts edition, Section 14.6, Eqs. 14.6.1–14.6.3 and the counting remark that follows. [Section 14.6](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/DeVoes_Thermodynamics_and_Chemistry/14%3A_Galvanic_Cells/14.06%3A_Standard_Electrode_Potentials)
- E. R. Cohen, T. Cvitaš, J. G. Frey, B. Holmström, K. Kuchitsu, R. Marquardt, I. Mills, F. Pavese, M. Quack, J. Stohner, H. L. Strauss, M. Takami and A. J. Thor, *Quantities, Units and Symbols in Physical Chemistry* (IUPAC Green Book), 3rd edition, RSC Publishing, 2007, Section 2.13, p. 71 ($E_{\mathrm{cell}}=E_{\mathrm R}-E_{\mathrm L}$). [doi:10.1039/9781847557889](https://doi.org/10.1039/9781847557889); [IUPAC PDF](https://iupac.org/wp-content/uploads/2019/05/IUPAC-GB3-2012-2ndPrinting-PDFsearchable.pdf)
- M. Z. Bazant, *10.626 Electrochemical Energy Systems*, MIT OpenCourseWare, Spring 2014, lecture notes, Lecture 8: The Nernst Equation, Sec. 5, Eq. (32) (standard open-circuit voltage as cathode minus anode standard potential). [Lecture PDF](https://old.ocw.mit.edu/courses/chemical-engineering/10-626-electrochemical-energy-systems-spring-2014/lecture-notes/MIT10_626S14_S11lec08.pdf); [course](https://ocw.mit.edu/courses/10-626-electrochemical-energy-systems-spring-2014/)
