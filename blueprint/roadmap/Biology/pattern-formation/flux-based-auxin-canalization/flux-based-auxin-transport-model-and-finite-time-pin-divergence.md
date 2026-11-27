# Flux-based auxin transport model and finite-time PIN divergence

**Model.** Cells $i\in V=\{1,\dots,M\}$ form a graph $\mathcal G=(V,E)$ with neighbours $i\sim j$. Let $a_i$ be the auxin concentration in cell $i$ and $p_{ij}$ the concentration of PIN carriers on the membrane of $i$ facing $j$. The net flux through membrane $ij$ is $J_{i\to j}=\gamma_D(a_i-a_j)+\gamma_A(a_ip_{ij}-a_jp_{ji})$ (diffusion plus active transport), and the flux model is

$$\frac{da_i}{dt}=\alpha_{a_i}-\beta_{a_i}a_i-\frac1{V_i}\sum_{j\sim i}S_{ij}J_{i\to j},\qquad \frac{dp_{ij}}{dt}=h(J_{i\to j})+\rho_0-\mu p_{ij},$$

with production and degradation rates $\alpha_{a_i},\beta_{a_i}$, membrane removal rate $\mu$, and a non-negative increasing response function $h$ with $h(J)=0$ for $J\le0$ (typically linear or quadratic in $J$).

**PIN-cycling model and reduced system.** The PIN-cycling variant of the model adds the cytosolic PIN concentration $P_i$ of cell $i$, produced at rate $\alpha_p$, degraded at rate $\beta_p$ and inserted into membrane $ij$ at rate $\lambda P_ih(J_{i\to j})$:

$$\frac{da_i}{dt}=\alpha_{a_i}-\beta_{a_i}a_i-\frac1{V_i}\sum_{j\sim i}S_{ij}J_{i\to j},\qquad \frac{dP_i}{dt}=\alpha_p-\beta_pP_i+\frac1{V_i}\sum_{j\sim i}S_{ij}\big(\mu p_{ij}-\lambda P_ih(J_{i\to j})\big),\qquad \frac{dp_{ij}}{dt}=\lambda P_ih(J_{i\to j})-\mu p_{ij}.$$

For regular cells ($S_{ij}/V_i\equiv W$) put $D=\gamma_DW$, $T=\gamma_AW$ and $\Phi(x)=h(x/W)$, and take $\alpha_p=\alpha_{p0}/\varepsilon$, $\beta_p=\beta_{p0}/\varepsilon$, $D=D_0\varepsilon$ and $T=1$ for a small $\varepsilon>0$ (fast cytosolic PIN turnover, diffusion negligible against active transport). Then $P_i=\alpha_p/\beta_p$ and the PIN-cycling model reduces to the slow system

$$\frac{da_i}{dt}=\alpha_{a_i}-\beta_{a_i}a_i+\sum_{k\sim i}\big(a_kp_{ki}-a_ip_{ik}\big),\qquad \frac{dp_{ij}}{dt}=\lambda\frac{\alpha_p}{\beta_p}\Phi(J_{i\to j})-\mu p_{ij},$$

with $J_{i\to j}=a_ip_{ij}-a_jp_{ji}$. If a solution of the slow system converges to an equilibrium, then for small enough $\varepsilon$ the solution of the PIN-cycling model with the same initial condition stays in a small neighbourhood of that slow solution for all $t\ge0$.

**Proposition.** If $\alpha_{a_i},\beta_{a_i},\mu,\lambda,\alpha_p/\beta_p>0$ and $\Phi$ is bounded, the slow system has a unique solution defined for all $t\ge0$. If $\Phi$ is unbounded, the solution either exists for all $t\ge0$ or only on a bounded interval $[0,\delta)$, on which it diverges to $\infty$ as $t\to\delta$; finite-time divergence of PIN concentrations does occur for unbounded $\Phi$ (e.g. quadratic).

## Expansion

Because $h$ vanishes for non-positive flux, at any equilibrium at most one of $p_{ij},p_{ji}$ is positive, so each steady state orients a subgraph of $\mathcal G$ ($i\to j$ iff $p^*_{ij}>0$). With a bounded response the PIN equation is linear with bounded forcing, so $p_{ij}$ stays bounded and global existence follows. With a superlinear response the feedback $p_{ij}\mapsto J_{i\to j}\propto p_{ij}\mapsto\Phi(J)\sim p_{ij}^2$ behaves like $\dot p=cp^2$, which explodes in finite time; the extreme PIN values that earlier simulations clipped as numerical artefacts are a property of the model.

## Sources

- C. Feller, E. Farcot, C. Mazza, "Self-organization of plant vascular systems: claims and counter-claims about the flux-based auxin transport model", *PLoS ONE* 10(3):e0118238 (2015), Results: equations (1), (2), (3a)–(3c) and (St0), sections "Model simplification" and "Divergence in finite time" (proofs in S1 Text), <https://doi.org/10.1371/journal.pone.0118238>, PMCID: PMC4348546.
