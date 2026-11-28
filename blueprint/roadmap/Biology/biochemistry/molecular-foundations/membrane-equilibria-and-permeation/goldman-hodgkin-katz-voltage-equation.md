# Goldman–Hodgkin–Katz voltage equation

The membrane potential at which the constant-field currents of $\mathrm K^+$, $\mathrm{Na}^+$ and $\mathrm{Cl}^-$ cancel is $V_r=\frac{RT}{F}\ln\frac{P_K[K]_{\mathrm{out}}+P_{Na}[Na]_{\mathrm{out}}+P_{Cl}[Cl]_{\mathrm{in}}}{P_K[K]_{\mathrm{in}}+P_{Na}[Na]_{\mathrm{in}}+P_{Cl}[Cl]_{\mathrm{out}}}$, a permeability-weighted generalization of the Nernst potential.

**Setting.** Monovalent ions $\mathrm K^+$, $\mathrm{Na}^+$ ($z=+1$) and $\mathrm{Cl}^-$ ($z=-1$) each obey the [GHK current equation](goldman-hodgkin-katz-current-equation.md) through the same membrane at the same voltage $V$ (inside minus outside), with fixed (voltage-independent) permeabilities $P_K,P_{Na},P_{Cl}\ge0$ (a species with zero permeability contributes identically zero current) and nonnegative concentrations, and no other current flows. Write

$$A=P_K[\mathrm K]_{\mathrm{out}}+P_{Na}[\mathrm{Na}]_{\mathrm{out}}+P_{Cl}[\mathrm{Cl}]_{\mathrm{in}},\qquad B=P_K[\mathrm K]_{\mathrm{in}}+P_{Na}[\mathrm{Na}]_{\mathrm{in}}+P_{Cl}[\mathrm{Cl}]_{\mathrm{out}},$$

and assume $A>0$ and $B>0$.

**Statement.** With $w=FV/RT$, the total current is

$$I_{\mathrm{tot}}=I_K+I_{Na}+I_{Cl}=F\cdot\frac{w}{e^{w}-1}\cdot\big(B\,e^{w}-A\big),$$

with the middle factor positive for all $w$ (extended by $1$ at $w=0$). Hence $I_{\mathrm{tot}}=0$ if and only if $V=V_r$, where

$$V_r=\frac{RT}{F}\ln\frac{A}{B};$$

the zero is unique, and $V_r=0$ exactly when $A=B$. This is zero net charge current, not zero flux of each ion.

Special cases: if only one species has positive permeability, $V_r$ is its [Nernst potential](../../../mathematical-neuroscience/nernst-potential-and-the-steady-state-cable-equa/nernst-potential.md) (for $\mathrm{Cl}^-$ the inside and outside concentrations exchange places, as $z=-1$ requires). In a bi-ionic arrangement with a permeant cation $X$ only outside and a permeant cation $Y$ only inside (sharing an impermeant anion), with $P_X[X]_{\mathrm{out}}>0$ and $P_Y[Y]_{\mathrm{in}}>0$ and all other terms zero,

$$V_r=\frac{RT}{F}\ln\frac{P_X[X]_{\mathrm{out}}}{P_Y[Y]_{\mathrm{in}}},$$

so the zero-current potential determines the permeability ratio $P_X/P_Y$. The formula is for monovalent ions; mixtures with divalent ions give a different expression.

## Context

Graduate physiology and biophysics. Hodgkin and Katz used the equation to show that the squid-axon membrane at rest is far more permeable to $\mathrm K^+$ than to $\mathrm{Na}^+$ and that the ratio reverses at the peak of the action potential; the fitted ratios ($P_K:P_{Na}:P_{Cl}=1:0.04:0.45$ at rest and $1:20:0.45$ at the peak) are empirical findings for that preparation, not consequences of the equation, and with voltage-dependent permeabilities the uniqueness statement above does not apply. The bi-ionic form is the standard way to measure channel selectivity.

## Depends on

- [Goldman–Hodgkin–Katz current equation](goldman-hodgkin-katz-current-equation.md)
- [Nernst potential of an ion species](../../../mathematical-neuroscience/nernst-potential-and-the-steady-state-cable-equa/nernst-potential.md)

## Proof depends on

None.

## Expansion

Proof: by the GHK current page, a cation contributes $P\,F\cdot\frac{w}{e^w-1}\cdot(C_{\mathrm{in}}e^w-C_{\mathrm{out}})$, and chloride (with $z=-1$, so its own variable is $-w$) contributes $-P\,F\cdot\frac{-w}{e^{-w}-1}\cdot(C_{\mathrm{in}}e^{-w}-C_{\mathrm{out}})=P\,F\cdot\frac{w}{e^w-1}\cdot(C_{\mathrm{out}}e^w-C_{\mathrm{in}})$. Summing gives the factored form. Since $w/(e^w-1)>0$ and $Be^w-A$ is strictly increasing in $w$ with a single zero at $w=\ln(A/B)$, the reversal potential exists and is unique; no separate monotonicity lemma is needed.

Remaining decomposition before the page can be marked ready: the identity $\frac{-w}{e^{-w}-1}=\frac{w\,e^{w}}{e^{w}-1}$ used for the anion term as a lemma, and the GHK current page's own decomposition (see its Expansion).

## Sources

- O. Alvarez and R. Latorre, "The enduring legacy of the 'constant-field equation' in membrane ion transport", *Journal of General Physiology* 149(10) (2017), 911–920; open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC5688357/), Introduction, Eq. 2 (GHK voltage equation, formally equivalent to Eq. 18 of Goldman 1943); section "The Goldman equation for zero-current potential", Eqs. 14–16; section "Monovalent cation selectivity measured in bi-ionic potential experiments", Eq. 18; section "Squid axon resting and action potential" (the empirical permeability ratios); section on mixtures of monovalent and divalent cations.
