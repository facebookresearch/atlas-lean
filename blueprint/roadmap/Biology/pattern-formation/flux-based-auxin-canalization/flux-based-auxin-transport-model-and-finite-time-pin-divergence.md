# Flux-based auxin transport model and finite-time PIN divergence

**Model.** Cells $i\in V=\{1,\dots,M\}$ form a graph $\mathcal G=(V,E)$ with neighbours $i\sim j$. Let $a_i$ be the auxin concentration in cell $i$ and $p_{ij}$ the concentration of PIN carriers on the membrane of $i$ facing $j$. The net flux through membrane $ij$ is $J_{i\to j}=\gamma_D(a_i-a_j)+\gamma_A(a_ip_{ij}-a_jp_{ji})$ (diffusion plus active transport), and the flux model is
$$\frac{da_i}{dt}=\alpha_{a_i}-\beta_{a_i}a_i-\frac1{V_i}\sum_{j\sim i}S_{ij}J_{i\to j},\qquad \frac{dp_{ij}}{dt}=h(J_{i\to j})+\rho_0-\mu p_{ij},$$
with production and degradation rates $\alpha_{a_i},\beta_{a_i}$, membrane removal rate $\mu$, and a non-negative increasing response function $h$ with $h(J)=0$ for $J\le0$ (typically linear or quadratic in $J$).

**Reduced system.** For regular cells ($S_{ij}/V_i\equiv W$), with PIN cycling and diffusion slow compared with active transport (rates of order $\varepsilon\to0$), unit transport efficiency and $\Phi(x)=h(x/W)$, the slow system is
$$\frac{da_i}{dt}=\alpha_{a_i}-\beta_{a_i}a_i+\sum_{k\sim i}\big(a_kp_{ki}-a_ip_{ik}\big),\qquad \frac{dp_{ij}}{dt}=\lambda\frac{\alpha_p}{\beta_p}\Phi(J_{i\to j})-\mu p_{ij},$$
with $J_{i\to j}=a_ip_{ij}-a_jp_{ji}$; trajectories of the full system with the same initial data stay close to those of the slow system for small $\varepsilon$ when the latter converge.

**Proposition.** If $\alpha_{a_i},\beta_{a_i},\mu,\lambda,\alpha_p/\beta_p>0$ and $\Phi$ is bounded, the slow system has a unique solution defined for all $t\ge0$. If $\Phi$ is unbounded, the solution either exists for all $t\ge0$ or only on a bounded interval $[0,\delta)$, on which it diverges to $\infty$ as $t\to\delta$; finite-time divergence of PIN concentrations does occur for unbounded $\Phi$ (e.g. quadratic).

## Expansion

Because $h$ vanishes for non-positive flux, at any equilibrium at most one of $p_{ij},p_{ji}$ is positive, so each steady state orients a subgraph of $\mathcal G$ ($i\to j$ iff $p^*_{ij}>0$). With a bounded response the PIN equation is linear with bounded forcing, so $p_{ij}$ stays bounded and global existence follows. With a superlinear response the feedback $p_{ij}\mapsto J_{i\to j}\propto p_{ij}\mapsto\Phi(J)\sim p_{ij}^2$ behaves like $\dot p=cp^2$, which explodes in finite time; the extreme PIN values that earlier simulations clipped as numerical artefacts are a property of the model.

## Sources

- C. Feller, E. Farcot, C. Mazza, "Self-organization of plant vascular systems: claims and counter-claims about the flux-based auxin transport model", *PLoS ONE* 10(3):e0118238 (2015), Results: equations (1), (2) and (St0), sections "Model simplification" and "Divergence in finite time" (proofs in S1 Text), <https://doi.org/10.1371/journal.pone.0118238>, PMCID: PMC4348546.
