# Unbound brain-to-plasma partition coefficient

Let $L_F(t)$ be the concentration of free (bioavailable) drug in brain capillary plasma and $L_M(t)$ the concentration of free drug in the brain extravascular space (interstitial and intracellular water, treated as one pool because brain cell membranes have about tenfold the surface area of the barrier). Let $V_p$ and $V_T$ be the plasma and tissue volumes of brain (about $10$ and $700\ \mu$L/g), $K_3$ the influx rate constant from capillary plasma to brain, $K_4$ the efflux rate constant from brain to blood, and $K_{\mathrm{met}}$ the rate constant of drug metabolism in brain. Drug binding to brain tissue proteins is reversible. At steady state,

$$\frac{L_M}{L_F} \;=\; \frac{K_3 V_p}{(K_4 + K_{\mathrm{met}})\, V_T},$$

independently of tissue binding. With $PS_{\mathrm{influx}} = K_3V_p$ and $PS_{\mathrm{efflux}} = K_4V_T$, and no brain metabolism, the unbound brain-to-plasma partition coefficient is

$$K_{p,uu} \;=\; \frac{L_M}{L_F} \;=\; \frac{PS_{\mathrm{influx}}}{PS_{\mathrm{efflux}}} .$$

So $K_{p,uu} = 1$ for symmetric transport (free diffusion of a lipid-soluble drug), $K_{p,uu} < 1$ indicates active efflux, and $K_{p,uu} > 1$ active influx. The influx PS product is measured after intravenous co-injection of the drug and a plasma-volume marker as

$$PS_{\mathrm{influx}} \;=\; \frac{(V_{D,\mathrm{test}} - V_{D,\mathrm{pv}})\, C_p(T)}{\int_0^T C_p(t)\,dt},$$

where $V_{D,\mathrm{test}}$ and $V_{D,\mathrm{pv}}$ are the brain volumes of distribution of the drug and of the marker at time $T$, valid while efflux is negligible.

## Depends on

- [Elimination rate constant](../one-compartment-linear-pharmacokinetics/elim-rate.md)

## Expansion

Mass balance for the free extravascular pool is $V_T\,\dot L_M = K_3V_pL_F - (K_4 + K_{\mathrm{met}})V_TL_M - (\text{net binding flux})$. At steady state the net binding flux vanishes, because binding equilibrium has no net exchange; setting $\dot L_M = 0$ gives the ratio, and $K_{\mathrm{met}} = 0$ gives $K_{p,uu}$. Tissue binding changes total brain drug but not the free concentration that acts on targets. For the influx measurement, early after injection the brain drug outside the vascular space is $PS_{\mathrm{influx}}\int_0^T C_p\,dt$ per gram. Dividing by the terminal plasma concentration gives $V_{D,\mathrm{test}} - V_{D,\mathrm{pv}}$, after subtracting the drug still inside the brain plasma volume. If this difference is zero, the molecule has not crossed the barrier: a common artefact in claims that intravenously injected antibodies enter the brain. The free capillary concentration $L_F$ can exceed the free fraction measured in vitro when bound drug dissociates faster in the capillary than in equilibrium dialysis, as quantified through the [Renkin–Crone extraction with plasma protein binding](renkin-crone-extraction-with-plasma-protein-binding.md).

## Sources

- W. M. Pardridge, "A historical review of brain drug delivery", *Pharmaceutics* 14(6) (2022) 1283, Section 11.1 ("Physiologic Model of Free Drug in Brain and Plasma", Equations (2)–(3)) and Section 11.4 (Equation (7)), <https://doi.org/10.3390/pharmaceutics14061283> (PMC9229021).
