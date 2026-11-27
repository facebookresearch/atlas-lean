# Outbreak probability for multiple pathogens across host species

**Model.** Host species $p = 1, \dots, P$ have susceptible $S_p$, latent $L_{pv}$ and infectious $I_{pv}$ individuals for each pathogen $v = 1, \dots, V$, and recovered $R_p$. With birth rate $b_p$, per-capita death rate $d_p$, cross-species transmission rates $\beta_{pqv}$ (infectious hosts of species $q$ infecting susceptibles of species $p$ with pathogen $v$), latency exit rates $\varepsilon_{pv}$ and recovery rates $\gamma_{pv}$,

$$
\begin{aligned}
\dot S_p &= b_p - \Bigl(\sum_{q=1}^{P}\sum_{v=1}^{V}\beta_{pqv} I_{qv} + d_p\Bigr) S_p, &
\dot L_{pv} &= \sum_{q=1}^{P}\beta_{pqv} I_{qv} S_p - (\varepsilon_{pv} + d_p) L_{pv},\\
\dot I_{pv} &= \varepsilon_{pv} L_{pv} - (\gamma_{pv} + d_p) I_{pv}, &
\dot R_p &= \sum_{v=1}^{V}\gamma_{pv} I_{pv} - d_p R_p .
\end{aligned}
$$

The disease-free equilibrium (DFE) has $S_p^0 = b_p/d_p$; $\mathcal{R}_0$ denotes the basic reproduction number of the system.

**Results.**
1. The DFE is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$; if $\mathcal{R}_0 < 1$ it is globally asymptotically stable in the feasible region.
2. *(Branching approximation.)* Near the DFE, latent and infectious individuals of each (species, pathogen) pair form a multitype branching process with offspring generating functions

$$
f^{\ell}_{pv}(\mathbf{u}) = \frac{\varepsilon_{pv} u^{i}_{pv} + d_p}{\varepsilon_{pv} + d_p}, \qquad
f^{i}_{pv}(\mathbf{u}) = \frac{\bigl(\sum_{q}\beta_{qpv} S^0_q u^{\ell}_{qv}\bigr) u^{i}_{pv} + \gamma_{pv} + d_p}{\Lambda_{pv}},
$$

with $\Lambda_{pv}$ the total event rate of an infectious individual. Starting from $\ell_{pv0}$ latent and $i_{pv0}$ infectious individuals,

$$
\mathbb{P}_{\mathrm{ext}} = \prod_{p=1}^{P}\prod_{v=1}^{V}\Bigl(\frac{\varepsilon_{pv} z^{i}_{pv} + d_p}{\varepsilon_{pv} + d_p}\Bigr)^{\ell_{pv0}} (z^{i}_{pv})^{i_{pv0}}, \qquad \mathbb{P}_{\mathrm{outbreak}} = 1 - \mathbb{P}_{\mathrm{ext}},
$$

where $\mathbf{z}$ is the minimal fixed point of the generating functions in $[0,1]^{2PV}$: $\mathbf{z} = \mathbf{1}$ if $\mathcal{R}_0 \le 1$, while for $\mathcal{R}_0 > 1$ there is a unique fixed point $\mathbf{0} < \mathbf{z} < \mathbf{1}$.
3. *(Two hosts, two pathogens.)* If pathogen 1 has $\mathcal{R}_{01} > 1$ and pathogen 2 has $\mathcal{R}_{02} \le 1$, the DFE is unstable and the system has a mixed equilibrium with pathogen 1 endemic and pathogen 2 absent, globally asymptotically stable with respect to the pathogen-2 subsystem.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

While susceptibles are near $S^0_p$, infected individuals act independently, so the epidemic is a multitype branching process whose types are (latent or infectious) × species × pathogen. A latent individual either progresses (probability $\varepsilon_{pv}/(\varepsilon_{pv} + d_p)$) or dies; an infectious one either infects a susceptible of some species (and remains infectious) or is removed. The extinction probability from one ancestor of each type is the minimal fixed point of the offspring generating functions, and independence of initial ancestors gives the product. The fixed point is below $\mathbf{1}$ exactly in the supercritical case, which coincides with $\mathcal{R}_0 > 1$ because the mean offspring matrix and the next-generation matrix share the same threshold.

## Related topics

- [Branching process approximation of early epidemics](../../branching-process-approximation-of-early-epidemi/README.md)

## Sources

- Clotilde Djuikem and Julien Arino, "Transmission of Multiple Pathogens Across Species", *Bulletin of Mathematical Biology* 87 (2025), 87, <https://doi.org/10.1007/s11538-025-01469-3>. Preprint version: arXiv:2405.20264 (2024), multi-species model, Lemma 1, Theorems 2–4, <https://doi.org/10.48550/arXiv.2405.20264>.
