# Donnan membrane equilibrium

When a membrane separates a salt solution from a solution containing an impermeant ion, for NaCl at $c_1$ against $\mathrm{R^+Cl^-}$ at $c_2$ in equal fixed volumes the NaCl concentration transferred at ideal equilibrium is $\alpha=c_1^2/(2c_1+c_2)$; for $c_2>0$ the ions distribute unequally, with $\phi_{\mathrm{II}}-\phi_{\mathrm I}=\frac{RT}{F}\ln(1+c_2/c_1)$.

**Setting.** Two compartments I and II of equal, fixed volume at a common temperature $T>0$ are separated by a membrane permeable to $\mathrm{Na^+}$ and $\mathrm{Cl^-}$ but not to the cation $\mathrm{R^+}$. Solvent exchange and pressure contributions to the ionic chemical potentials are neglected (common reference pressure), both bulk solutions are electrically neutral, and activities are replaced by concentrations (ideal solutions). Initially I contains NaCl at concentration $c_1>0$ and II contains $\mathrm{R^+Cl^-}$ at $c_2\ge0$. At equilibrium a concentration $\alpha$ of NaCl has moved from I to II:

$$\text{I: }[\mathrm{Na^+}]=[\mathrm{Cl^-}]=c_1-\alpha;\qquad \text{II: }[\mathrm{Na^+}]=\alpha,\ [\mathrm{R^+}]=c_2,\ [\mathrm{Cl^-}]=c_2+\alpha.$$

**Statement.**

1. Equality of the electrochemical potentials of $\mathrm{Na^+}$ and of $\mathrm{Cl^-}$ across the membrane implies equality of the chemical potential of the neutral salt (the electrical terms cancel in the sum), which is the Donnan product rule

$$[\mathrm{Na^+}]_{\mathrm I}[\mathrm{Cl^-}]_{\mathrm I}=[\mathrm{Na^+}]_{\mathrm{II}}[\mathrm{Cl^-}]_{\mathrm{II}},\qquad (c_1-\alpha)^2=\alpha\,(c_2+\alpha),$$

whose unique solution with $0<\alpha<c_1$ is

$$\alpha=\frac{c_1^2}{2c_1+c_2},\qquad \frac{\alpha}{c_1}=\frac{c_1}{2c_1+c_2}.$$

So $\alpha/c_1=1/2$ (equal distribution) only when $c_2=0$, and $\alpha/c_1$ decreases toward $0$ as $c_2$ grows.

2. The individual ion equilibria then fix the membrane potential $\Delta\phi=\phi_{\mathrm{II}}-\phi_{\mathrm I}$:

$$\Delta\phi=\frac{RT}{F}\ln\frac{[\mathrm{Na^+}]_{\mathrm I}}{[\mathrm{Na^+}]_{\mathrm{II}}}=\frac{RT}{F}\ln\frac{c_1-\alpha}{\alpha}=\frac{RT}{F}\ln\!\left(1+\frac{c_2}{c_1}\right)\ge0,$$

and the $\mathrm{Cl^-}$ equilibrium gives the same value by the product rule. Compartment II, holding the impermeant cation, is at the higher potential for $c_2>0$ (the potentials are equal at $c_2=0$); replacing $\mathrm{R^+}$ by an analogous monovalent impermeant anion reverses the sign, and other valences require the general form $z_iF\Delta\phi=RT\ln(c_{i,\mathrm I}/c_{i,\mathrm{II}})$ rather than this uni-univalent algebra.

With a solvent-permeable membrane and free volumes, solvent would also have to equilibrate, which in general produces an osmotic pressure difference or a volume change; that is outside this fixed-volume model.

## Context

Undergraduate to graduate physiology and physical biochemistry. The principal application is to charged macromolecules (proteins, nucleic acids, polyelectrolyte gels) that cannot cross a membrane: their counter-ions are retained and small ions distribute unequally, which also produces an osmotic-pressure difference and a membrane potential. Charged polymer systems such as the cationic dendrimer–anionic RNA complexes and aldehyde-dextran hydrogels used by the Artzi laboratory (Conde et al. 2016) are polyelectrolyte systems where Donnan effects can arise, but that paper does not analyze them; the relevance is conceptual.

## Depends on

- [Molar electrochemical potential of an ion species](../../../mathematical-neuroscience/nernst-potential-and-the-steady-state-cable-equa/electrochemical-potential.md)

## Proof depends on

None.

## Expansion

Proof: with ideal electrochemical potentials $\mu_i=\mu_i^\circ+RT\ln(c_i/c^\circ)+z_iF\phi$, equality for $\mathrm{Na^+}$ ($z=1$) and $\mathrm{Cl^-}$ ($z=-1$) across the membrane gives item 2 directly, and adding the two equalities eliminates $\phi$ and gives the product rule. Expanding, $c_1^2-2\alpha c_1=\alpha c_2$ is linear in $\alpha$. Substituting $\alpha$ gives $(c_1-\alpha)/\alpha=(c_1+c_2)/c_1$. The equal-volume assumption is implicit in the source's bookkeeping (the same $\alpha$ is lost from I and gained by II); unequal volumes change the conservation relation but not the product rule.

Remaining decomposition before the page can be marked ready: (i) the fixed-volume, neglected-pressure model as an explicit definition; (ii) a page for the general multi-ion, multi-valence Donnan equilibrium (needed before any statement about other valences), and (iii) the coupled osmotic problem as a separate page.

## Sources

- M. J. Blandamer and J. C. R. Reis, *Topics in Thermodynamics of Solutions and Liquid Mixtures*, LibreTexts, Section 1.14.21 "Donnan Membrane Equilibria" (read at [chem.libretexts.org](https://chem.libretexts.org/Bookshelves/Physical_and_Theoretical_Chemistry_Textbook_Maps/Topics_in_Thermodynamics_of_Solutions_and_Liquid_Mixtures/01%3A_Modules/1.24%3A_Misc/1.14.21%3A_Donnan_Membrane_Equilibria)): the two-compartment set-up at common $T$ and $p$, the chemical-potential equality, the product relation, Donnan's equation $\alpha^{\mathrm{eq}}/c_1=c_1/(2c_1+c_2)$ and its footnote derivation (the membrane potential in item 2 is derived on this page, not stated in the source).
- J. Conde, N. Oliva, M. Atilano, H. S. Song and N. Artzi, "Self-assembled RNA-triple-helix hydrogel scaffold for microRNA modulation in the tumour microenvironment", *Nature Materials* 15(3) (2016), 353–363, [doi.org](https://doi.org/10.1038/nmat4497); author manuscript read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC6594154/) (context only: electrostatic complexation of cationic dendrimer amines with RNA phosphates).
