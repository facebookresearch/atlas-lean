# Higuchi pseudo-steady-state release from a planar matrix

For a non-swelling planar matrix with dispersed drug at loading $A \gg C_s$ releasing into a perfect sink, the pseudo-steady model gives released amount per area $M(t) = \sqrt{D(2A - C_s)C_s t}$ while the dissolution front is inside the matrix.

Consider a planar matrix of thickness $L$ releasing through one face $x = 0$ into a perfect sink, containing drug at total loading $A$ per unit volume with $A > C_s > 0$, the solubility in the matrix, and diffusivity $D > 0$. Assume the matrix neither swells nor erodes, edge effects are negligible, and behind a receding front at $x = h(t)$ the drug is fully dissolved with a linear profile from $C_s$ at the front to $0$ at the surface (pseudo-steady state, justified when $A \gg C_s$). Then, for $0 < h(t) < L$,

$$M(t) = \sqrt{D(2A - C_s)C_s\,t}, \qquad h(t)^2 = \frac{2DC_s t}{A - C_s/2}.$$

The front reaches the back face at $t_f = (A - C_s/2)L^2/(2DC_s)$, when $M = (A - C_s/2)L$, less than the total load $AL$ because dissolved drug remains; release after $t_f$ is a different (purely diffusive) phase.

## Context

Undergraduate pharmaceutics and transport. Higuchi derived the law in 1961 for ointment films; Siepmann and Peppas stress that its constant has a physical meaning only under these assumptions and that applying it to swelling or eroding systems, such as many hydrogels, is a misuse. A $\sqrt t$ fit alone does not establish this mechanism: [Fickian release of dissolved drug](fickian-release-from-a-slab.md) also starts as $\sqrt t$. The open web rendering of the source's Eq. (29) loses the square root; the dimensions (mass per area) and the abstract restore it.

## Depends on

None.

## Proof depends on

None.

## Expansion

Derivation: released amount equals the depleted loading minus the dissolved drug still in the linear profile, $M = (A - C_s/2)h$; the surface flux is $DC_s/h$; equating $dM/dt$ to the flux gives $h\,dh/dt = DC_s/(A - C_s/2)$ and the formulas. The exact sharp-front problem replaces the linear profile by $c_t = Dc_{xx}$ with front condition $Dc_x = (A - C_s)\,dh/dt$; its similarity solution parallels the [Neumann solution of the one-phase Stefan problem](../../../../Analysis/partial-differential-equations/one-phase-stefan-problem/neumann-similarity-solution-of-the-one-phase-stefan-problem.md) and recovers Higuchi's law as $A/C_s \to \infty$. Both, and the post-front phase, need pages.

## Sources

- C. Mircioiu, V. Voicu, V. Anuta, A. Tudose, C. Celia, D. Paolino, M. Fresta, R. Sandulovici and I. Mircioiu, "Mathematical Modeling of Release Kinetics from Supramolecular Drug Delivery Systems", Pharmaceutics 11(3), 140 (2019), <https://doi.org/10.3390/pharmaceutics11030140>; open-access copy read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC6471682/>: Section 3.1.2 (Higuchi's model, Figure 7, Eq. (29) and the condition $A \gg C_s$; the exact solutions attributed to Carslaw and Jaeger, Chapter XI, and to Koizumi et al. 1975)
- J. Siepmann and N. A. Peppas, "Higuchi equation: derivation, applications, use and misuse", International Journal of Pharmaceutics 418, 6–12 (2011), <https://doi.org/10.1016/j.ijpharm.2011.03.051>; only the abstract was read, at <https://pubmed.ncbi.nlm.nih.gov/21458553/>: abstract: pseudo-steady-state derivation, thin ointment films with finely dispersed drug, perfect sink, physical meaning of the constant, and use and misuse
