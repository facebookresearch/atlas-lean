# Saturable carrier-mediated transport with competing substrates

Let a substrate at plasma concentration $S$ cross the blood–brain barrier by a saturable carrier with maximal velocity $V_{\max}$ and absolute half-saturation constant $K_m$, in parallel with a nonsaturable pathway of clearance constant $K_{NS}$. Then the permeability–surface area product and unidirectional influx are

$$PS(S) \;=\; \frac{V_{\max}}{K_m + S} + K_{NS}, \qquad J(S) \;=\; PS(S)\cdot S \;=\; \frac{V_{\max}S}{K_m + S} + K_{NS}S .$$

If competing substrates $i$, at plasma concentrations $S_i$, share the carrier with absolute constants $K_i$ (competitive inhibition), then $K_m$ is replaced by the apparent constant

$$K_{m,\mathrm{app}} \;=\; K_m\Bigl(1 + \sum_i \frac{S_i}{K_i}\Bigr).$$

Consequences: $PS$ is decreasing in $S$ and in every $S_i$; when $S \ll K_m$ and $S_i \ll K_i$, $PS \approx V_{\max}/K_m + K_{NS}$ and no competition is felt. When plasma concentrations are comparable to the $K_m$ values, as for the large neutral amino acids on the LAT1 carrier, raising one substrate (for instance phenylalanine in phenylketonuria) lowers the brain influx of all the others. In the brain uptake index method, $V_{\max}$, $K_m$ and $K_{NS}$ are estimated by nonlinear regression of the clearance $\mathrm{BUI}\cdot E_{\mathrm{ref}}\cdot F$ on $S$.

## Depends on

- [Renkin–Crone extraction with plasma protein binding](renkin-crone-extraction-with-plasma-protein-binding.md)

## Expansion

Michaelis–Menten carrier flux is $V_{\max}S/(K_m + S)$, and dividing by $S$ gives a clearance (PS) contribution $V_{\max}/(K_m + S)$; the nonsaturable pathway adds a constant clearance. With competitive substrates binding the same site, the fraction of free carrier is $1/(1 + S/K_m + \sum_i S_i/K_i)$. The test-substrate flux is therefore

$$\frac{V_{\max}\,S/K_m}{1 + S/K_m + \sum_i S_i/K_i} \;=\; \frac{V_{\max}\,S}{K_m(1 + \sum_i S_i/K_i) + S},$$

which is the Michaelis–Menten form with $K_m$ replaced by $K_{m,\mathrm{app}}$. Monotonicity in $S$ and $S_i$ is immediate from the formula. The barrier carrier for neutral amino acids has high affinity, with $K_m$ close to plasma concentrations, unlike low-affinity peripheral transporters, which explains the selective vulnerability of the brain to hyperaminoacidaemias.

## Sources

- W. M. Pardridge, "A historical review of brain drug delivery", *Pharmaceutics* 14(6) (2022) 1283, Section 11.4.1 ("Brain Uptake Index Method", "Carrier-mediated transport", Equations (5)–(6)), <https://doi.org/10.3390/pharmaceutics14061283> (PMC9229021).
