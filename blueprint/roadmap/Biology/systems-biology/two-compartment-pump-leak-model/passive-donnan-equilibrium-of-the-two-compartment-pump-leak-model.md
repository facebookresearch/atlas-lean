# Passive Donnan equilibrium of the two-compartment pump–leak model

**Setting.** Two compartments $j \in \{A, B\}$ (an intracellular compartment and a lumen) exchange $\mathrm{Na}^+$, $\mathrm{K}^+$, $\mathrm{Cl}^-$ and water with each other and with an infinite extracellular bath $e$, through membranes and a paracellular pathway with ion conductances $g_{\mathrm{ion},eA}, g_{\mathrm{ion},AB}, g_{\mathrm{ion},eB} \ge 0$ and water permeabilities $\nu_{eA}, \nu_{AB}, \nu_{eB} \ge 0$. Compartment $j$ has volume $w_j$, membrane potential $V_j$, ion concentrations $[\mathrm{Na}]_j, [\mathrm{K}]_j, [\mathrm{Cl}]_j$ and a fixed amount $X_j$ of impermeant solute of valence $z_j$, at concentration $[X]_j = X_j/w_j$. The bath has concentrations $[\mathrm{Na}]_e, [\mathrm{K}]_e, [\mathrm{Cl}]_e > 0$, an impermeant solute $[Y]_e > 0$ of valence $z_Y$, is electroneutral, and has total osmolarity $O_e$. Each compartment is electroneutral and ion fluxes follow linear current–voltage laws driven by $V_j - E_{\mathrm{ion},j}$, $E_{\mathrm{ion},j}$ being the Nernst potential.

**Assumption 1 (passive system).** No active transport (all pump rates zero); for each ion at least two of $g_{\mathrm{ion},eA}, g_{\mathrm{ion},AB}, g_{\mathrm{ion},eB}$ are positive; at least two of $\nu_{eA}, \nu_{AB}, \nu_{eB}$ are positive.

**Lemma 1.** Let $C_{eq}^2 = [\mathrm{Cl}]_e\big([\mathrm{Na}]_e + [\mathrm{K}]_e\big)$ and

$$\xi_j = \begin{cases} \dfrac{O_e - \sqrt{4(1 - z_j^2)C_{eq}^2 + z_j^2 O_e^2}}{1 - z_j^2}, & z_j^2 \ne 1,\\[2ex] \dfrac{O_e^2 - 4C_{eq}^2}{2O_e}, & z_j^2 = 1. \end{cases}$$

Then $4C_{eq}^2 < O_e^2$ and $\xi_j > 0$.

**Proposition 1.** Under Assumption 1 the system has a stable equilibrium with $[X]_j^{eq} = \xi_j$ and, for $j \in \{A, B\}$,

$$[\mathrm{Cl}]_j^{eq} = \tfrac12\big(O_e + (z_j - 1)\xi_j\big), \qquad [\mathrm{Na}]_j^{eq} = \frac{2[\mathrm{Na}]_e[\mathrm{Cl}]_e}{O_e + (z_j-1)\xi_j}, \qquad [\mathrm{K}]_j^{eq} = \frac{2[\mathrm{K}]_e[\mathrm{Cl}]_e}{O_e + (z_j-1)\xi_j},$$

$$w_j^{eq} = \frac{X_j}{\xi_j}, \qquad V_j^{eq} = \frac{RT}{F}\ln\frac{O_e + (z_j-1)\xi_j}{2[\mathrm{Cl}]_e}.$$

## Expansion

Setting the ion fluxes to zero in both compartments and using that at least two conductances per ion are positive forces $V_j^{eq} = E_{\mathrm{ion},j}^{eq}$ for every ion and both compartments (Eq. 14): each ion is in electrochemical equilibrium with the bath, so $[\mathrm{Na}]_j/[\mathrm{Na}]_e = [\mathrm{K}]_j/[\mathrm{K}]_e = [\mathrm{Cl}]_e/[\mathrm{Cl}]_j$ (the Donnan ratio). Zero water flux with at least two positive water permeabilities forces equal osmolarities, $[\mathrm{Na}]_j + [\mathrm{K}]_j + [\mathrm{Cl}]_j + [X]_j = O_e$ (Eq. 17). Electroneutrality, $[\mathrm{Na}]_j + [\mathrm{K}]_j - [\mathrm{Cl}]_j + z_j[X]_j = 0$, combined with osmotic balance gives $[\mathrm{Cl}]_j = \tfrac12(O_e + (z_j-1)[X]_j)$ and $[\mathrm{Na}]_j + [\mathrm{K}]_j = \tfrac12(O_e - (z_j+1)[X]_j)$. The Donnan ratio gives $[\mathrm{Cl}]_j([\mathrm{Na}]_j + [\mathrm{K}]_j) = C_{eq}^2$, i.e.

$$(1 - z_j^2)[X]_j^2 - 2O_e[X]_j + O_e^2 - 4C_{eq}^2 = 0,$$

whose admissible root is $\xi_j$; positivity follows from $4C_{eq}^2 < O_e^2$, which holds because the bath contains impermeant solute. The equilibrium is the same as for a single cell in the bath: the lumen does not alter the passive Donnan state, only the volumes $w_j = X_j/\xi_j$ differ. With the Na$^+$/K$^+$-ATPase active the steady state becomes a pump-dependent perturbation of this state (Proposition 2).

## Sources

- K. Tarrant, A. R. Kay, Z. Aminzare, "Stability and Robustness of a Generalized Pump-Leak Model for Epithelial Vesicles", Bulletin of Mathematical Biology (2026), Assumption 1, Lemma 1, Proposition 1 and Eqs. (9)–(17), <https://doi.org/10.1007/s11538-026-01683-7>, PMCID PMC13369021.
