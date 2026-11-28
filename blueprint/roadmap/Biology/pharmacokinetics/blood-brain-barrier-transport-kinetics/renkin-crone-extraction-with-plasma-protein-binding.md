# Renkin–Crone extraction with plasma protein binding

Let a solute pass through a capillary bed with plasma flow $F$ and capillary permeability–surface area product $PS$, assume plug flow, negligible back-flux during a single pass, and binding of the solute in plasma to a protein at concentration $A$ (in excess over the solute) with $n$ independent binding sites of dissociation constant $K_D$, in rapid equilibrium relative to transit. Then the unidirectional extraction fraction of a single pass is

$$E \;=\; 1 - \exp\Bigl(-f\,\frac{PS}{F}\Bigr), \qquad f \;=\; \frac{K_D/n}{A + K_D/n},$$

where $f$ is the free fraction. Without binding ($f = 1$) this is the Renkin–Crone (Kety–Renkin–Crone) equation $E = 1 - e^{-PS/F}$; for small $PS/F$, $E \approx PS/F$, and $E \to 1$ as $PS/F \to \infty$. Fitting $E$ measured at several protein concentrations $A$ by nonlinear regression estimates both $PS/F$ and the in-vivo dissociation constant $K_D/n$. In the brain uptake index method, a carotid bolus of the test solute with a freely diffusible reference is used, and $E_{\mathrm{test}} = \mathrm{BUI}\cdot E_{\mathrm{ref}}$, where $\mathrm{BUI}$ is the ratio of test-to-reference radioactivity in brain divided by the same ratio in the injectate.

## Expansion

Along the capillary, at fractional position $x \in [0,1]$, only free solute crosses the wall, so the total concentration obeys $F\,dC/dx = -PS\cdot fC$, and integrating gives $C(1)/C(0) = e^{-fPS/F}$, the fraction that escapes extraction. With $n$ sites per protein molecule and protein in excess, the site concentration is $nA$, and binding equilibrium gives bound/free $= nA/K_D$, so the free fraction is $1/(1 + nA/K_D)$, the displayed $f$. The extraction is a concave, increasing function of transit time $V/F$ at fixed $PS$, the property behind the cost of capillary transit time heterogeneity. For many albumin- or $\alpha_1$-acid glycoprotein-bound drugs and hormones, the $K_D$ estimated in vivo greatly exceeds the equilibrium-dialysis value (for testosterone on bovine albumin, about $2520$ versus $53\ \mu$M). This indicates enhanced dissociation at the endothelial surface: the free hormone hypothesis fails, and protein-bound drug is partly available for transport. Measured $PS/F$ ratios of $0.14$–$1.35$ are far too small for a dissociation-limited mechanism.

## Sources

- W. M. Pardridge, "A historical review of brain drug delivery", *Pharmaceutics* 14(6) (2022) 1283, Section 11.2 ("Free Drug in Plasma In Vivo and Role of Plasma Protein Binding", Equation (4), Table 5) and Section 11.4.1 ("Brain Uptake Index Method"), <https://doi.org/10.3390/pharmaceutics14061283> (PMC9229021).
