# Higuchi pseudo-steady-state release from a planar matrix

For a non-swelling planar matrix with dispersed drug at loading $A \gg C_s$ releasing into a perfect sink, the pseudo-steady model gives released amount per area $M(t) = \sqrt{D(2A - C_s)C_s t}$ while the dissolution front is inside the matrix.

Consider a planar matrix of thickness $L$ releasing through one face $x = 0$ into a perfect sink, containing drug at total loading $A$ per unit volume with $A > C_s > 0$, the solubility in the matrix, and diffusivity $D > 0$. Assume the matrix neither swells nor erodes, edge effects are negligible, the dispersed drug particles are much smaller than the matrix thickness and dissolve locally so that a sharp boundary separates an inner region containing undissolved particles from an outer, particle-free region, and behind this receding front at $x = h(t)$ the drug is fully dissolved with a linear profile from $C_s$ at the front to $0$ at the surface (pseudo-steady state, justified when $A \gg C_s$). Then, for $0 < h(t) < L$,

$$M(t) = \sqrt{D(2A - C_s)C_s\,t}.$$

## Context

Undergraduate pharmaceutics and transport. Higuchi derived the law in 1961 for ointment films. Siepmann and Peppas (abstract) highlight the assumptions of the derivation, note that the constant has a specific, physically realistic meaning, and review the equation's use and potential misuse; Dash et al. list among the hypotheses that matrix swelling and dissolution are negligible. A $\sqrt t$ fit alone does not establish this mechanism (compare [Fickian release of dissolved drug](fickian-release-from-a-slab.md)). The open text renderings of Mircioiu et al. (Eq. (29)), Dash et al. (Eq. (7)) and Paul (Eq. (1)) all flatten the radical. The square-root dependence on time is stated in the Siepmann–Peppas abstract and in Dash et al.'s simplified form $Q = K_H t^{1/2}$ (their Eq. (9)); Paul's publicly displayed section on the accuracy of the pseudo-steady approximation gives the flux $DC_s/\xi$ through the depleted zone and the global mass balance $dM_t/dt = (A - C_s/2)\,d\xi/dt$ (his Eqs. (3)–(4)), which together give the displayed law.

## Depends on

None.

## Proof depends on

None.

## Expansion

Derivation: released amount equals the depleted loading minus the dissolved drug still in the linear profile, $M = (A - C_s/2)h$; the surface flux is $DC_s/h$; equating $dM/dt$ to the flux gives $h^2 = 2DC_st/(A - C_s/2)$ and the formula. The same balance gives the time at which the front reaches the back face and the amount then released; release after that time is a separate, purely diffusive phase, and both need their own statements. The exact sharp-front problem replaces the linear profile by $c_t = Dc_{xx}$ with front condition $Dc_x = (A - C_s)\,dh/dt$; its similarity solution parallels the [Neumann solution of the one-phase Stefan problem](../../../../Analysis/partial-differential-equations/one-phase-stefan-problem/neumann-similarity-solution-of-the-one-phase-stefan-problem.md) and recovers Higuchi's law as $A/C_s \to \infty$. Both, and the post-front phase, need pages.

## Sources

- C. Mircioiu, V. Voicu, V. Anuta, A. Tudose, C. Celia, D. Paolino, M. Fresta, R. Sandulovici and I. Mircioiu, "Mathematical Modeling of Release Kinetics from Supramolecular Drug Delivery Systems", Pharmaceutics 11(3), 140 (2019), <https://doi.org/10.3390/pharmaceutics11030140>; open-access copy read at <https://pmc.ncbi.nlm.nih.gov/articles/PMC6471682/>: Section 3.1.2 (Higuchi's model, Figure 7, Eq. (29) and the condition $A \gg C_s$; the exact solutions attributed to Carslaw and Jaeger, Chapter XI, and to Koizumi et al. 1975)
- J. Siepmann and N. A. Peppas, "Higuchi equation: derivation, applications, use and misuse", International Journal of Pharmaceutics 418, 6–12 (2011), <https://doi.org/10.1016/j.ijpharm.2011.03.051>; only the abstract was read, at <https://pubmed.ncbi.nlm.nih.gov/21458553/>: abstract: pseudo-steady-state derivation, proportionality between cumulative release and the square root of time, thin ointment films with finely dispersed drug, perfect sink, physical meaning of the constant, and "the use and potential misuse of this equation"
- S. Dash, P. N. Murthy, L. Nath and P. Chowdhury, "Kinetic modeling on drug release from controlled drug delivery systems", Acta Poloniae Pharmaceutica – Drug Research 67(3), 217–223 (2010), publisher PDF at <https://ptfarm.pl/pub/File/Acta_Poloniae/2010/3/217.pdf>, read through an indexed text extraction in which the radical's extent is flattened: section "Higuchi model": hypotheses (i)–(vi) (initial concentration much higher than solubility, one-dimensional diffusion, drug particles much smaller than system thickness, negligible swelling and dissolution, constant diffusivity, perfect sink), Eq. (7) (written there with the release area and $C$ for the initial concentration) and Eq. (9), $Q = K_H t^{1/2}$
- D. R. Paul, "Elaborations on the Higuchi model for drug delivery", International Journal of Pharmaceutics 418, 13–17 (2011), publisher page <https://www.sciencedirect.com/science/article/pii/S0378517310008124>; only the publicly displayed abstract, introduction and section snippets were read: Introduction (inner region with undissolved particles and outer particle-free region separated by a moving boundary; $M_t$ per unit area of surface; Eq. (1)) and the publicly displayed snippet of the section "Accuracy of the pseudosteady-state approximation" (Eq. (3), $J = dM_t/dt = DC_s/\xi$ from a steady-state Fick's first law with $C = 0$ at $x = 0$; Eq. (4), the global mass balance $dM_t/dt = (A - C_s/2)\,d\xi/dt$; "Eqs. (3), (4) can be combined and integrated to get Eqs. (1) or (2)"); fractions are flattened in the page's text rendering
