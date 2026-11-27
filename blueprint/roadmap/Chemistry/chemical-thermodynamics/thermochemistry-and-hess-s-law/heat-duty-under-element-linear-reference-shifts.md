# Heat duty under element-linear reference shifts

Consider an open reactor at constant pressure and volume whose species amounts satisfy the open elemental balance hypotheses
($n' = F_{\mathrm{in}} - F_{\mathrm{out}} + N w$ with $AN = 0$), with contents and streams at the same temperature and an ideal
mixture. Assume that kinetic and potential energy are neglected in both the storage and streams and that shaft work is zero.
Then the supplied first law gives the heat duty

$$\dot Q = \frac{d}{dt}\sum_j n_j \bar H_j + \sum_j \bigl(F_{\mathrm{out},j} - F_{\mathrm{in},j}\bigr)\bar H_j$$

in terms of the molar enthalpies $\bar H_j$, used with the same reference for storage and streams. Shifting every molar enthalpy by
an element-linear constant, $\bar H_j \mapsto \bar H_j + \sum_b A_{bj} a_b$, leaves $\dot Q$ unchanged: the change is
$a^{\mathsf T}\bigl(\frac{d}{dt} A n - A(F_{\mathrm{in}} - F_{\mathrm{out}})\bigr) = 0$. A shift that is not element-linear can change
the duty: for the isomerization $A \to B$ in a closed vessel, shifting $\bar H_B$ alone by $\delta \ne 0$ changes $\dot Q$ by
$\delta\, n_B'(t)$, which is nonzero while the reaction proceeds. This is the counterpart, for heat duties, of the invariance of
reaction enthalpies under such shifts; in steady operation it reduces to the reference-state invariance of the adiabatic
enthalpy residual.

More generally, the same reference-shift cancellation holds when shaft-work, kinetic/potential-energy and $(PV)'$ terms are
retained: these terms do not change under the reference shift. Contents, inlet and outlet temperatures need not agree, provided
each species uses the same temperature-independent shift in every stream and in the stored energy; the stored internal-energy
shift is $a^{\mathsf T} A n$. The change in computed duty is still the displayed elemental-balance residual.

## Depends on

- [Open first law with kinetic and potential energy](../../../Physics/thermodynamics-and-heat-transfer/thermodynamic-systems-and-cycles/open-first-law-with-kinetic-and-potential-energy.md), for the enthalpy form of the duty

## Proof depends on

- [Open elemental balance](../../amounts-and-stoichiometry/process-material-balances/open-elemental-balance.md)

## Sources

- J. B. Rawlings and J. G. Ekerdt, *Chemical Reactor Analysis and Design Fundamentals*, 2nd edition, paperback, seventh printing (November 2026), Nob Hill Publishing; freely distributed by the authors at <https://sites.engineering.ucsb.edu/~jbraw/chemreacfun/> (page numbers below are the printed ones): Section 6.1, Equation 6.5 and Section 6.2, the explicit kinetic/potential-energy and shaft-work omissions (pp. 275–276); Equations 6.10–6.14 (pp. 277–278), the enthalpy of the contents through partial molar enthalpies and the heat of reaction $\Delta H_{Ri} = \sum_j \nu_{ij} \bar H_j$; Exercise 2.8, Equation 2.67 (pp. 58–59).
