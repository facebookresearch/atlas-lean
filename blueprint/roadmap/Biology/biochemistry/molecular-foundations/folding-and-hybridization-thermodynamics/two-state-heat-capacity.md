# Heat capacity of a two-state unfolding transition

In the two-state model the excess heat capacity relative to the native baseline is $C_p(T)=\Delta H(T)\,d\Theta_U/dT+\Theta_U\Delta C_p$; with $\Delta C_p=0$ it is $\Theta_U(1-\Theta_U)\Delta H^2/(RT^2)$, which equals $\Delta H^2/(4RT_m^2)$ at the midpoint, and its integral over a temperature window is $\Delta H$ times the change in unfolded fraction.

**Setting.** Two-state unfolding with unfolded fraction $\Theta_U(T)=K/(1+K)$, $T>0$, and unfolding enthalpy $\Delta H(T)$ as on the [protein stability curve](protein-stability-curve.md). The excess (transition) enthalpy per mole of protein, relative to the native baseline, is $\Theta_U(T)\,\Delta H(T)$.

**Statement.**

1. The excess heat capacity is

$$C_p(T)=\frac{d\big(\Theta_U\Delta H\big)}{dT}=\Delta H(T)\,\frac{d\Theta_U}{dT}+\Theta_U(T)\,\Delta C_p,\qquad \frac{d\Theta_U}{dT}=\Theta_U(1-\Theta_U)\frac{\Delta H(T)}{RT^2},$$

and for any window $T_1<T_2$, $\int_{T_1}^{T_2}C_p\,dT=\big[\Theta_U\Delta H\big]_{T_1}^{T_2}$.

2. When $\Delta C_p=0$ (constant $\Delta H,\Delta S$) with $\Delta H>0$ and midpoint $T_m=\Delta H/\Delta S>0$,

$$C_p(T)=\frac{\Delta H^2}{RT^2}\,\Theta_U(1-\Theta_U),\qquad C_p(T_m)=\frac{\Delta H^2}{4RT_m^2},\qquad \int_{T_1}^{T_2}C_p\,dT=\Delta H\,\big(\Theta_U(T_2)-\Theta_U(T_1)\big).$$

Since $\Theta_U(T)\to1/(1+e^{-\Delta S/R})<1$ as $T\to\infty$, for $\Delta C_p=0$ the integrated area is $\Delta H\,\Delta\Theta_U$ and only approximates $\Delta H$ when the window's endpoint fractions are effectively $0$ and $1$ and the baselines are consistent (for general $\Delta C_p$ the area is $[\Theta_U\Delta H]$ between the endpoints).

Agreement between the calorimetric enthalpy (from the area) and the van 't Hoff enthalpy (from the shape) is the usual operational test of the two-state assumption; agreement is consistent with the model but does not prove it.

## Context

Graduate biophysics. Differential scanning calorimetry is the reference method for protein and nucleic-acid stability; the model-independent integrals of the measured $C_p(T)$ (Seelig and Seelig, Eqs. 1–3) give $\Delta H$, $\Delta S$ and $\Delta G$ relative to a reference state, and the two-state equation above is the simplest model fitted to them.

## Depends on

- [Protein stability curve with constant heat-capacity change](protein-stability-curve.md)
- [Two-state unfolding equilibrium and the van 't Hoff slope at the melting temperature](two-state-unfolding-and-the-van-t-hoff-slope.md)

## Proof depends on

None.

## Expansion

Proof: item 1 is the product rule together with $d\ln K/dT=\Delta H(T)/(RT^2)$, which holds with temperature-dependent $\Delta H$ because $d(\Delta G/T)/dT=-\Delta H/T^2$; the integral is the fundamental theorem of calculus. Item 2 substitutes $\Delta C_p=0$. Seelig and Seelig state the product-rule formula (their Eq. 12) as the hallmark of the two-state model; the closed form at $\Delta C_p=0$ combines it with their Eq. 5.

Derived here and not stated in the cited sources (a candidate separate page), under the hypotheses of item 2 (constant $\Delta H>0$ and a positive midpoint $T_m$): an interior maximum $T_{\mathrm{peak}}$ of $C_p$ satisfies $(1-2\Theta_U(T_{\mathrm{peak}}))\,\Delta H/(RT_{\mathrm{peak}})=2$, (from $\frac{d}{dT}\big[\Theta_U(1-\Theta_U)T^{-2}\big]=\Theta_U(1-\Theta_U)T^{-2}\big[(1-2\Theta_U)\Delta H/(RT^2)-2/T\big]$), so $\Theta_U<1/2$ there and $T_{\mathrm{peak}}<T_m$; with $\Delta H/(RT_m)=2$ it lies near $0.59\,T_m$ at about $1.8$ times $C_p(T_m)$ (checked numerically). The identification of the maximum with $T_m$ is therefore approximate.

Remaining decomposition before the page can be marked ready: (i) a source for the location of the $C_p$ maximum, with existence and uniqueness of the interior maximum, before it enters a statement; (ii) a precise definition of the native-baseline excess heat capacity used by calorimetry, which is a modelling convention.

## Sources

- J. Seelig and A. Seelig, "Protein unfolding—thermodynamic perspectives and unfolding models", *International Journal of Molecular Sciences* 24(6) (2023), 5457, [www.mdpi.com](https://www.mdpi.com/1422-0067/24/6/5457); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC10049513/), Section 2.1, Eqs. 1–3 and the baseline discussion (model-independent DSC integrals) and Section 2.2, Eqs. 5, 11 and 12 (van 't Hoff equation; unfolded fraction; heat capacity of the chemical-equilibrium two-state model).
- M. E. Tuckerman, *Physical Chemistry for Biological Sciences*, LibreTexts (DePaul University), Section 13.7 "The van 't Hoff Equation" (read at [chem.libretexts.org](https://chem.libretexts.org/Courses/DePaul_University/Physical_Chemistry_for_Biological_Sciences/13%3A_Chemical_Equilibrium/13.07%3A_The_van_'t_Hoff_Equation)): $(\partial\ln K/\partial T)_P=\Delta H^\circ/RT^2$ from the Gibbs–Helmholtz equation, which item 1 uses with a temperature-dependent $\Delta H$.
- H. Jakubowski and P. Flatt, *Fundamentals of Biochemistry*, LibreTexts, Section 4.12 "Laboratory Determination of the Thermodynamic Parameters for Protein Denaturation" (read at [bio.libretexts.org](https://bio.libretexts.org/Bookshelves/Biochemistry/Fundamentals_of_Biochemistry_%28Jakubowski_and_Flatt%29/01:_Unit_I-_Structure_and_Catalysis/04:_The_Three-Dimensional_Structure_of_Proteins/4.12:_Laboratory_Determination_of_the_Thermodynamic_Parameters_for_Protein_Denaturation)), learning goals on comparing van 't Hoff and calorimetric enthalpies (that page identifies the $C_p$ maximum with $T_m$, which holds only approximately).
