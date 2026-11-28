# Two-state unfolding equilibrium and the van 't Hoff slope at the melting temperature

For a two-state transition $N\rightleftharpoons U$ with temperature-independent $\Delta H^\circ$ and $\Delta S^\circ$, the unfolded fraction is $K/(1+K)$ with $K=e^{-\Delta G^\circ/RT}$, the van 't Hoff relation $d\ln K/dT=\Delta H^\circ/RT^2$ holds, and when $T_m=\Delta H^\circ/\Delta S^\circ>0$ the melting curve has slope $\Delta H^\circ/(4RT_m^2)$ there.

**Setting.** A macromolecule exists in a native state $N$ and an unfolded state $U$ only (two-state model) in ideal dilute solution, so the unimolecular equilibrium constant is a concentration ratio. The standard free energy of unfolding is $\Delta G^\circ(T)=\Delta H^\circ-T\Delta S^\circ$ with $\Delta H^\circ$ and $\Delta S^\circ$ independent of temperature, $R$ is the gas constant in units matching $\Delta H^\circ$, and $T>0$ is the absolute temperature. The equilibrium constant and the unfolded fraction are

$$K(T)=\frac{[U]}{[N]}=e^{-\Delta G^\circ(T)/RT},\qquad \Theta_U(T)=\frac{K(T)}{1+K(T)}.$$

**Statement.**

1. For every $T>0$,

$$\frac{d\ln K}{dT}=\frac{\Delta H^\circ}{RT^2},\qquad \frac{d\Theta_U}{dT}=\Theta_U(1-\Theta_U)\,\frac{\Delta H^\circ}{RT^2},$$

and for any reference temperature $T_{\mathrm{ref}}>0$, $K(T)=K(T_{\mathrm{ref}})\exp\!\big[-\frac{\Delta H^\circ}{R}\big(\frac1T-\frac1{T_{\mathrm{ref}}}\big)\big]$.

2. A unique midpoint $\Theta_U(T)=1/2$ at some $T>0$ exists if and only if $\Delta S^\circ\neq0$ and $\Delta H^\circ/\Delta S^\circ>0$; it is $T_m=\Delta H^\circ/\Delta S^\circ$, and there $K=1$ and $\Delta G^\circ=0$. If $\Delta H^\circ=\Delta S^\circ=0$, every $T>0$ is a midpoint and there is no distinguished $T_m$; otherwise there is no midpoint.

3. When $T_m>0$ exists,

$$K(T)=\exp\!\left[-\frac{\Delta H^\circ}{R}\left(\frac1T-\frac1{T_m}\right)\right],\qquad \left.\frac{d\Theta_U}{dT}\right|_{T=T_m}=\frac{\Delta H^\circ}{4RT_m^2}.$$

For endothermic unfolding ($\Delta H^\circ>0$, $\Delta S^\circ>0$) the unfolded fraction rises with temperature; the steepness at $T_m$ measures the van 't Hoff enthalpy.

## Context

Undergraduate physical biochemistry. The same two-state analysis is applied to protein unfolding, ligand binding and nucleic-acid melting. Bimolecular duplex melting is treated by the [concentration-dependent duplex melting temperature](two-state-duplex-melting-temperature.md) rather than the unimolecular result here; higher-order association needs its own mass balances and is outside both pages.

## Depends on

None.

## Proof depends on

None.

## Expansion

Proof: $\ln K=-\Delta H^\circ/(RT)+\Delta S^\circ/R$ gives item 1 by differentiation (using $d\Theta_U/dK=(1+K)^{-2}$ and $dK/dT=K\,d\ln K/dT$) and by integration from $T_{\mathrm{ref}}$. Item 2: $\Theta_U=1/2$ iff $\ln K=0$ iff $\Delta H^\circ=T\Delta S^\circ$, which has exactly one positive solution when $\Delta S^\circ\neq0$ and $\Delta H^\circ/\Delta S^\circ>0$, holds for all $T$ when both constants vanish, and has no positive solution otherwise. Item 3 is item 1 with $T_{\mathrm{ref}}=T_m$, $K(T_m)=1$ and $\Theta_U(T_m)=1/2$.

Source notes. Seelig and Seelig use the unfolding direction as here. Tokmakoff uses the folding direction: with $K=[F]/[U]=e^{-\Delta G^\circ_{\mathrm{fold}}/RT}$ the folded fraction is $\phi_F=K/(1+K)=1/(1+e^{+\Delta G^\circ_{\mathrm{fold}}/RT})$, and $\Delta H^\circ_{\mathrm{fold}}=-\Delta H^\circ$. Two slips in that page were verified independently: its first logistic equality prints $e^{-\Delta G^0/RT}$ in the denominator, inconsistent with its own $K$ (its expanded form has the correct sign), and it prints $d\phi_F/dK=K^{-2}(1+K)^{-2}$, whereas the correct value is $(1+K)^{-2}$ (at $K=2$ these are $1/36$ and $1/9$); the two agree only at $K=1$, which is why its final midpoint slope is right.

Remaining decomposition before the page can be marked ready: a definition page for the ideal unimolecular two-state equilibrium (relating $K$ to $\Delta G^\circ$ with the standard-state convention), on which this page's statements are lemmas.

## Sources

- A. Tokmakoff, *Concepts in Biophysical Chemistry*, LibreTexts, Section 18.2 "Two-State Thermodynamics" (read at [chem.libretexts.org](https://chem.libretexts.org/Bookshelves/Biological_Chemistry/Concepts_in_Biophysical_Chemistry_%28Tokmakoff%29/05%3A_Cooperativity/18%3A_Cooperativity/18.02%3A_Two-State_Thermodynamics)): $K=\phi_F/(1-\phi_F)$, $T_m=\Delta H^0/\Delta S^0$, the van 't Hoff analysis and the midpoint slope $\Delta H^0/(4RT_m^2)$ (folding direction).
- J. Seelig and A. Seelig, "Protein unfolding—thermodynamic perspectives and unfolding models", *International Journal of Molecular Sciences* 24(6) (2023), 5457, [www.mdpi.com](https://www.mdpi.com/1422-0067/24/6/5457); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC10049513/), Section 2.2, Eqs. 4–7 and 11 ($K_{NU}=[U]/[N]$, the van 't Hoff equation and its integral, $\Theta_U=K_{NU}/(1+K_{NU})$).
- M. E. Tuckerman, *Physical Chemistry for Biological Sciences*, LibreTexts (DePaul University), Section 13.7 "The van 't Hoff Equation" (read at [chem.libretexts.org](https://chem.libretexts.org/Courses/DePaul_University/Physical_Chemistry_for_Biological_Sciences/13%3A_Chemical_Equilibrium/13.07%3A_The_van_'t_Hoff_Equation)): the general relation $(\partial\ln K/\partial T)_P=\Delta H^\circ/RT^2$ obtained from the Gibbs–Helmholtz equation, with the integrated form valid when $\Delta H^\circ$ can be treated as constant.
