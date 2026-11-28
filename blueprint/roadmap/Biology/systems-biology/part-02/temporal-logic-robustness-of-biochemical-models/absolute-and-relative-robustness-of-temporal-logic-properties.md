# Absolute and relative robustness of temporal-logic properties

**Setting.** Let a biochemical model (for example an ODE system) produce a numerical trace $T_p$ for each perturbation $p$ in a set $P$ of perturbations of parameters or initial conditions, with probability law $\mathrm{prob}$ on $P$, and let the function to be maintained be specified by an LTL formula $\phi$ with continuous satisfaction degree $sd(T, \phi) = 1/(1 + vd(T, \phi))$. Let $p^*$ be the nominal (unperturbed) parameter.

**Definitions.**

- *Absolute robustness* (Kitano's definition with the satisfaction degree as evaluation function):

    $$R_{\phi, P} = \int_{P} sd(T_p, \phi)\, \mathrm{prob}(p)\, dp \qquad \Big(= \sum_{p \in P} sd(T_p, \phi)\, \mathrm{prob}(p) \text{ for discrete } P\Big).$$

- *Relative robustness* with respect to the nominal behaviour:

    $$R_{\phi, P}^{\mathrm{rel}} = \frac{R_{\phi, P}}{sd(T_{p^*}, \phi)} .$$

- *Distance from robust satisfaction:* $\mathrm{dist}\big(\bigcap_{p} \mathcal D_{T_p, \phi(y)},\ y^\phi\big)$, the smallest change of the constants of $\phi$ after which it holds under every perturbation.

**Properties.** $R_{\phi,P} \in (0, 1]$, with $R_{\phi,P} = 1$ iff $\phi$ holds for almost every perturbation (when the satisfaction domains are closed). Absolute robustness is the mean functionality under perturbations, while relative robustness measures how much perturbations degrade the nominal performance: two systems whose performance functions $p \mapsto sd(T_p, \phi)$ have the same mean have equal absolute robustness even if one loses much more relative to its nominal value, and multiplying a performance function by a constant leaves relative robustness unchanged. The two notions answer different questions and should not be used interchangeably. $R$ is estimated by Monte Carlo sampling of $p$, and the satisfaction-degree landscape over parameter space can be explored for design.

## Expansion

Kitano defined robustness as the probability-weighted average of a problem-specific evaluation function but left that function unspecified; using $sd$ makes the definition generic for any property expressible in LTL with numerical constraints. The bounds follow from $0 < sd \le 1$. Applied to a synthetic transcriptional cascade with 5000 log-normally distributed parameter vectors in a 16-dimensional space, the method quantified how robustly the cascade is "well-timed"; over a two-parameter grid the robustness landscape is a blurred version of the satisfaction-degree landscape, and relative robustness highlights regions where the satisfaction degree changes sharply. The method is implemented in the BIOCHAM modelling environment.

## Depends on

- [Satisfaction domain and violation degree of LTL formulae on numerical traces](satisfaction-domain-and-violation-degree-of-ltl-formulae-on-numerical-traces.md)

## Sources

- A. Rizk, G. Batt, F. Fages, S. Soliman, "A general computational method for robustness analysis with applications to synthetic gene networks", Bioinformatics 25 (2009), i169–i178, Section 3.1 (Eqs. (3)–(4)), Section 3.2 (Eq. (5), Fig. 2), Section 3.3 ("Robust satisfaction degree") and Section 4, <https://doi.org/10.1093/bioinformatics/btp200> (PMC2687954).
- H. Kitano, "Towards a theory of biological robustness", Molecular Systems Biology 3 (2007), 137, <https://doi.org/10.1038/msb4100179>.
