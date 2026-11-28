# Thermodynamically feasible flux for given chemical potentials

A flux is thermodynamically feasible for given chemical potentials when every active internal reaction runs in the direction of decreasing Gibbs energy; exchange reactions and inactive reactions are not constrained.

Let $M$ (species) and $R$ (reactions) be finite, $S\in\mathbb{R}^{M\times R}$ a stoichiometric matrix, and let $R=I\sqcup E$ split the reactions into **internal** reactions $I$ (chemical transformations or transports between modelled compartments) and **exchange** reactions $E$ (uptake, secretion, biomass drain, chemostatted supply). For **chemical potentials** $\mu\in\mathbb{R}^M$, supplied as data, the Gibbs energy of the internal reaction $r\in I$ is

$$\Delta_rG(\mu)=\sum_{m\in M}S_{mr}\,\mu_m=(S^{\mathsf T}\mu)_r .$$

A flux $v\in\mathbb{R}^R$ is **thermodynamically feasible for $\mu$** when

$$v_r\,\Delta_rG(\mu)<0\qquad\text{for every }r\in I\text{ with }v_r\ne0 .$$

Equivalently, for each internal $r$: $\Delta_rG(\mu)<0$ forces $v_r\ge0$, $\Delta_rG(\mu)>0$ forces $v_r\le0$, and $\Delta_rG(\mu)=0$ forces $v_r=0$. A flux is **thermodynamically feasible** when it is feasible for some $\mu\in\mathbb{R}^M$.

Conventions: $\mu$ is in energy per amount (for instance $\mu_m=\mu_m^\circ+RT\ln(c_m/c^\circ)$ for an ideal dilute species with $c_m>0$ and concentration standard $c^\circ>0$, or the transformed potential at fixed pH), $S$ has products positive, and the sign of $v_r$ is relative to the written direction. For charged transport, use electrochemical potentials including $z_mF\psi_{\mathrm{compartment}(m)}$, where $z_m$ is charge number, $F$ the Faraday constant and $\psi$ the compartment electric potential. A transformed convention must use each compartment's specified pH consistently; do not combine a transformed proton reservoir with an untransformed proton-transport energy. Feasibility for $\mu$ is unchanged if $\mu$ is replaced by $\lambda\mu+\eta$ with $\lambda>0$ and $\eta\in\mathbb{R}^M$ satisfying $\sum_mS_{mr}\eta_m=0$ for every $r\in I$ (for instance $\eta$ constant on species when every internal reaction conserves the total number of molecules), and if $v$ is replaced by $\lambda v$ with $\lambda>0$. The condition is imposed on internal reactions only: a nonzero steady flux in a closed network would itself be a sign-compatible internal cycle, which the [loop law](loopless-iff-exists-chemical-potential.md) excludes.

## Depends on

None.

## Proof depends on

None.

## Expansion

The equivalent form is a case split on the sign of $\Delta_rG(\mu)$. Invariance: $\Delta_rG(\lambda\mu+\eta)=\lambda\Delta_rG(\mu)+\sum_mS_{mr}\eta_m=\lambda\Delta_rG(\mu)$ for internal $r$, and multiplying $v$ by $\lambda>0$ multiplies each product $v_r\Delta_rG(\mu)$ by $\lambda$.

De Martino et al. write the condition as $\mu\Omega>0$ with $\Omega_{mr}=-\operatorname{sign}(v_r)S_{mr}$ over the internal reactions with nonzero flux, after excluding uptakes, biomass production and reactions without a thermodynamic constraint; that is exactly the inequality above. The feasibility notion requires the existence of potentials, not realistic values; adding concentration or formation-energy ranges for $\mu$ is a further restriction.

## Sources

- D. De Martino, F. Capuani, M. Mori, A. De Martino and E. Marinari, Counting and correcting thermodynamically infeasible flux cycles in genome-scale metabolic networks, *Metabolites* 3 (2013), 946–966, [doi:10.3390/metabo3040946](https://doi.org/10.3390/metabo3040946): Section 1, Equations (1) and (2) and the definition of $\Omega$ preceding Equation (2).
- A. Kümmel, S. Panke and M. Heinemann, Systematic assignment of thermodynamic constraints in metabolic network models, *BMC Bioinformatics* 7 (2006), article 512, [doi:10.1186/1471-2105-7-512](https://doi.org/10.1186/1471-2105-7-512): Results, Equation (1) (reaction Gibbs energy from formation energies and concentrations).
