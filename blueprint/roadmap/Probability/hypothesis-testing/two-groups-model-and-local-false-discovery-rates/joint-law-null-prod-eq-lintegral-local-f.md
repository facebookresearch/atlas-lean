# Null probability as an integral of the local fdr

In a [two-groups model](two-groups-model.md), for every measurable $A \subseteq \mathbb{R}$,

$$P(H = 0, Z \in A) = \int_A \operatorname{fdr}(z)\, dP_Z(z),$$

where $P_Z$ is the law of the z-value under the [joint law](joint-law.md). Hence $\operatorname{fdr}(Z)$ is a version of the posterior null probability $P(H = 0 \mid Z)$ (Efron et al. 2001).
