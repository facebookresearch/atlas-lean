# Learned and derived pattern rivalry in a four-node Wilson network

**Model.** Four nodes $ij \in \{11, 21, 12, 22\}$ each carry an activity $x_{ij}^E$ and a fatigue variable $x_{ij}^H$. With equal inputs $I$, a nondecreasing gain function $G$, learned-pattern excitation $w > 0$, lateral excitation $\delta \ge 0$, reciprocal inhibition $\beta > 0$, fatigue strength $g > 0$ and time-scale ratio $\varepsilon$, the network (System 11) is

$$\varepsilon \dot x_{11}^E = -x_{11}^E + G\big(I + w x_{22}^E + \delta x_{12}^E - \beta x_{21}^E - g x_{11}^H\big), \qquad \dot x_{11}^H = x_{11}^E - x_{11}^H,$$

and the analogous equations obtained by the index permutations, so that $\{11, 22\}$ and $\{21, 12\}$ are the two **learned patterns** (joined by $w$), $11 \leftrightarrow 12$ and $21 \leftrightarrow 22$ are lateral pairs (joined by $\delta$), and $11 \leftrightarrow 21$, $12 \leftrightarrow 22$ are rival pairs (joined by $\beta$). The **derived patterns** $\{11, 12\}$ and $\{21, 22\}$ were not learned.

**Linearization.** At a fusion equilibrium $x_{ij}^E = x_{ij}^H = x_0$, with $G' = G'(I + (w + \delta - \beta - g)x_0)$, the symmetry splits the Jacobian into four $2 \times 2$ blocks $J_{\pm\pm}$ on the isotypic components, with traces (Equation 17)

$$\operatorname{tr} J_{++} = -1 + (w + \delta - \beta)G' - \varepsilon,\quad \operatorname{tr} J_{+-} = -1 - (w + \delta + \beta)G' - \varepsilon,$$

$$\operatorname{tr} J_{-+} = -1 + (\beta + \delta - w)G' - \varepsilon,\quad \operatorname{tr} J_{--} = -1 + (\beta + w - \delta)G' - \varepsilon .$$

A Hopf bifurcation occurs when one trace vanishes with positive determinant; it is stable when all four determinants are positive and the other three traces negative. Oscillation in $J_{--}$ alternates the two learned patterns; oscillation in $J_{-+}$ alternates the two derived patterns.

**Proposition 2 (learned-pattern rivalry).** Stable Hopf bifurcation to learned-pattern rivalry requires $\beta > \delta$ and $w > \delta$. Together with $g > w - \delta + \beta$ and $G' > 1/(w - \delta + \beta)$ these conditions are sufficient, and the bifurcation occurs at $\varepsilon = -1 + (w - \delta + \beta)G' > 0$.

**Proposition 3 (derived-pattern rivalry).** Stable Hopf bifurcation to derived-pattern rivalry requires $\beta > w$ and $\delta > w$. Together with $g > \delta - w + \beta$ and $G' > 1/(\delta - w + \beta)$ these conditions are sufficient, and the bifurcation occurs at $\varepsilon = -1 + (\delta - w + \beta)G' > 0$.

## Expansion

The network is invariant under a symmetry group permuting nodes that preserves each coupling type, so its linearization at the symmetric fusion state is block diagonal on the group's isotypic components, each block being the $2 \times 2$ activity-fatigue system with an effective coupling $\pm w \pm \delta - \beta$-type eigenvalue of the connectivity matrix. Requiring the chosen trace to vanish fixes $\varepsilon$; substituting it into the other traces gives the necessary inequalities, and positivity of determinants gives the sufficient ones. The two propositions are mutually exclusive in the coupling strengths: derived-pattern rivalry needs lateral coupling stronger than learned-pattern excitation, which is why adding lateral connections, inspired by cortical architecture, lets the model reproduce interocular-grouping percepts observed in rivalry experiments.

## Sources

- C. O. Diekman, M. Golubitsky, Y. Wang, "Derived patterns in binocular rivalry networks", Journal of Mathematical Neuroscience 3 (2013) 6, Equations (10), (11), (17)–(24), Propositions 2–3, <https://doi.org/10.1186/2190-8567-3-6> (PMC3698087).
