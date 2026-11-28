# Duality of the diffusive contact process with open boundaries

**Model.** On the chain $\Lambda_N = \{1,\dots,N\}$ each site is healthy ($\eta_x = 0$) or infected ($\eta_x = 1$). The *open diffusive contact process* (DCP) has generator

$$
\mathcal{L}^{\mathrm{DCP}} = \mathcal{L}_- + \mathcal{L}^{\mathrm{CP}} + \mathcal{D}\,\mathcal{L}^{\mathrm{SSEP}} + \mathcal{L}_+,
$$

where $\mathcal{L}^{\mathrm{CP}}$ is the contact process (a healthy site is infected at rate $\lambda$ times its number of infected neighbours, an infected site recovers at rate $1$), $\mathcal{L}^{\mathrm{SSEP}}$ is the symmetric simple exclusion process (infected individuals move to a healthy neighbouring site at rate $1$ per bond, scaled by $\mathcal{D} > 0$), and the boundaries are reservoirs: site $1$ is infected at rate $\alpha$ when healthy and cured at rate $\gamma$ when infected, site $N$ is infected at rate $\delta$ and cured at rate $\beta$.

**Statement.** The open DCP is dual to a *purely absorbing* contact process $(\xi_t)$ on $\Omega_N^{\mathrm{dual}} = \mathbb{N}_0 \times \{0,1\}^{\Lambda_N} \times \mathbb{N}_0$, where the extra coordinates $\xi_0, \xi_{N+1}$ count particles absorbed in sinks at sites $0$ and $N+1$. The duality function is

$$
D(\eta,\xi) = \Bigl(\frac{\gamma}{\alpha + \gamma}\Bigr)^{\xi_0}\ \prod_{x \in \Lambda_N}(1 - \eta_x)^{\xi_x}\ \Bigl(\frac{\beta}{\beta + \delta}\Bigr)^{\xi_{N+1}},
$$

that is, $\mathbb{E}_\eta[D(\eta_t,\xi)] = \mathbb{E}_\xi[D(\eta,\xi_t)]$, and the dual generator is

$$
\mathcal{L}^{\mathrm{dual}} = \mathcal{L}^{\mathrm{CP}} + \mathcal{D}\,\mathcal{L}^{\mathrm{SSEP}} + \mathcal{L}^{\mathrm{dual}}_- + \mathcal{L}^{\mathrm{dual}}_+,
$$

with $\mathcal{L}^{\mathrm{dual}}_- f(\xi) = (\alpha + \gamma)\xi_1[f(\xi^{1,0}) - f(\xi)]$ and $\mathcal{L}^{\mathrm{dual}}_+ f(\xi) = (\beta + \delta)\xi_N[f(\xi^{N,N+1}) - f(\xi)]$ (a particle at an edge site jumps into the adjacent sink).

So the open DCP is ergodic but no longer absorbing (the reservoirs reinfect it), while its dual is absorbing but not ergodic. Stationary correlations of the open DCP are therefore expressed through absorption probabilities of the dual: since the bulk of the dual empties almost surely, for $A \subseteq \Lambda_N$ the stationary probability that all sites of $A$ are healthy is $\mathbb{E}\bigl[(\gamma/(\alpha+\gamma))^{\xi_0(\infty)}(\beta/(\beta+\delta))^{\xi_{N+1}(\infty)}\bigr]$ for the dual started from one particle on each site of $A$ and empty sinks.

## Expansion

In the bulk the contact process and the exclusion process are both self-dual with the factorized function $H(\eta,\xi) = \prod_x(1 - \eta_x)^{\xi_x}$, and so is their sum. At an edge, applying the reservoir generator to $1 - \eta_1$ gives $\alpha(1-\eta_1)\cdot(-1) + \gamma\eta_1 = \gamma - (\alpha + \gamma)(1 - \eta_1)$, which is $(\alpha + \gamma)\bigl[\frac{\gamma}{\alpha+\gamma} - (1 - \eta_1)\bigr]$: the action of a dual particle that jumps at rate $\alpha + \gamma$ into a sink where it contributes the constant factor $\gamma/(\alpha+\gamma)$. Since dual particles are created by the contact dynamics and destroyed by recovery or absorption, the dual eventually has an empty bulk, and letting $t \to \infty$ in the duality relation gives the stationary correlations.

## Sources

- Chiara Franceschini, Ellen Saada, Gunter M. Schütz and Sonia Velasco, "Duality for some models of epidemic spreading", Stochastic Processes and their Applications 191 (2026), 104773, <https://doi.org/10.1016/j.spa.2025.104773>; numbering as in arXiv:2408.15613: Section 2, Theorem 1.
