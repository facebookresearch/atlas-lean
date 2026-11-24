# Formation-enthalpy duty equals sensible heat plus reaction heat

Consider a steady flow of an ideal mixture of species $i = 1, \dots, N$, with no heat of mixing, in which one reaction with
stoichiometric coefficients $\nu_i$ runs to extent $\xi$, so that the outlet molar flows are $n_i^{\mathrm{out}} = n_i^{\mathrm{in}} + \nu_i \xi$. Fix one
reference temperature $T_0$ and one standard state. Give each species its standard formation enthalpy $\Delta_f H_i^\circ$ at $T_0$,
relative to the same element reference states, and a constant molar heat capacity $c_{p,i}$, so that its molar enthalpy is
$h_i(T) = \Delta_f H_i^\circ + c_{p,i}(T - T_0)$, with no phase change. Define the formation-enthalpy duty
$Q = \sum_i n_i^{\mathrm{out}} h_i(T_{\mathrm{out}}) - \sum_i n_i^{\mathrm{in}} h_i(T_{\mathrm{in}})$ and the reaction enthalpy $\Delta_r H(T) = \sum_i \nu_i h_i(T)$, so that
$\Delta_r H(T_0) = \sum_i \nu_i \Delta_f H_i^\circ$. Then

$$Q = \sum_i n_i^{\mathrm{out}} c_{p,i} (T_{\mathrm{out}} - T_0) - \sum_i n_i^{\mathrm{in}} c_{p,i} (T_{\mathrm{in}} - T_0) + \xi\, \Delta_r H(T_0)
= \sum_i n_i^{\mathrm{in}} c_{p,i} (T_{\mathrm{out}} - T_{\mathrm{in}}) + \xi\, \Delta_r H(T_{\mathrm{out}}),$$

where $\Delta_r H(T) = \Delta_r H(T_0) + \Delta c_p\, (T - T_0)$ with $\Delta c_p = \sum_i \nu_i c_{p,i}$, Kirchhoff's law for constant heat capacities.

- The reaction term depends only on the product $\xi\, \Delta_r H$: multiplying every $\nu_i$ by $2$ doubles $\Delta_r H$ and halves the extent
  that gives the same outlet flows, so the term is unchanged.
- Adding the reaction heat $\xi\, \Delta_r H(T_0)$ to the formation-enthalpy duty $Q$ counts it twice: the sum exceeds $Q$ by
  $\xi\, \Delta_r H(T_0)$, which is nonzero whenever $\xi \ne 0$ and $\Delta_r H(T_0) \ne 0$.

Proof: substituting $n_i^{\mathrm{out}} = n_i^{\mathrm{in}} + \nu_i \xi$ and $h_i$ into $Q$, the formation terms combine to $\xi \sum_i \nu_i \Delta_f H_i^\circ$, which
gives the first form. Writing $Q = \sum_i n_i^{\mathrm{in}} \bigl(h_i(T_{\mathrm{out}}) - h_i(T_{\mathrm{in}})\bigr) + \xi \sum_i \nu_i h_i(T_{\mathrm{out}})$ gives the second.

## Proof depends on

- [Kirchhoff's law](kirchhoff-law.md)
- [Scaling a reaction scales its enthalpy](hess-smul.md)

## Sources

- Wikipedia, "Standard enthalpy of reaction", revision of 11 October 2026: the reaction enthalpy as the stoichiometric sum of
  standard formation enthalpies, the convention that elements in their standard states have zero enthalpy, and Kirchhoff's law of
  thermochemistry. The stream balance and the two forms of the duty are derived on this page.
