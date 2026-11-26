# Allee bistability in a stage-structured mosquito model with Holling type-II mating

**Model.** A sex- and stage-structured mosquito model tracks eggs $E$, larvae $L$, pupae $P$, unmated females $F_u$, females mated with wild males $F_{mw}$ or with sterile males $F_{ms}$, wild males $M_w$ and sterile males $M_s$:

$$\begin{aligned}
\dot E &= \phi\Big(1-\tfrac{E}{K_E}\Big)F_{mw} - (\sigma_E+\mu_E)E, &\quad \dot L &= \sigma_E E - (\sigma_L+\mu_L+\delta_L L)L,\\
\dot P &= \sigma_L L - (\sigma_P+\mu_P)P, &\quad \dot F_u &= r\sigma_P P - \frac{M_w+\eta M_s}{\gamma+\zeta(M_w+\eta M_s)}F_u - \mu_F F_u,\\
\dot F_{mw} &= \frac{M_w}{\gamma+\zeta(M_w+\eta M_s)}F_u - \mu_F F_{mw}, &\quad \dot F_{ms} &= \frac{\eta M_s}{\gamma+\zeta(M_w+\eta M_s)}F_u - \mu_F F_{ms},\\
\dot M_w &= (1-r)\sigma_P P - \mu_M M_w, &\quad \dot M_s &= S(t) - \mu_M M_s,
\end{aligned}$$

with nonnegative parameters, positive mortalities, egg capacity $K_E$, larval competition $\delta_L$, mate-search constant $\gamma>0$, refractory period $\zeta$, and sterile-male release rate $S(t)\ge 0$. The Holling type-II mating term vanishes linearly as $M_w\to 0$, producing a mate-finding Allee effect. $\mathcal{R}_0^{q}$ denotes the basic reproduction number of the quick-mate-search model obtained by setting $\gamma=0$.

**Theorem (no releases, $S\equiv 0$).**

1. The mosquito-free equilibrium $\mathcal{E}_0$ is locally asymptotically stable for all admissible parameter values.
2. If $\mathcal{R}_0^{q}<1$, $\mathcal{E}_0$ is globally asymptotically stable in the feasible region.
3. If $\mathcal{R}_0^{q}>1$, there are thresholds $K_E^{*}>0$ and $\delta_L^{*}>0$ such that for $K_E>K_E^{*}$ and $\delta_L<\delta_L^{*}$ there are exactly two positive equilibria $X_-^{**}\le X_+^{**}$ (componentwise), and for $K_E$ larger and $\delta_L$ smaller still (thresholds $K_E^{**}\ge K_E^{*}$, $\delta_L^{**}\le\delta_L^{*}$) the natural equilibrium $X_+^{**}$ is locally asymptotically stable and the Allee equilibrium $X_-^{**}$ is unstable.

The two positive equilibria arise in a saddle–node bifurcation, and $X_-^{**}$ lies on the separatrix between persistence and extinction.

## Expansion

Near $\mathcal{E}_0$ the mating rate is $O(M_w)$, so the linearised production of mated females vanishes and every eigenvalue is negative: extinction is always locally stable, unlike in models with linear mating. With $\gamma=0$ the mating term saturates and the usual threshold behaviour returns, which is why $\mathcal{R}_0^{q}$ controls global extinction. Reducing the equilibrium conditions to a scalar equation in $M_w$ shows two positive roots when capacity is large and competition weak.

## Sources

- A. Gumel, C. A. Safsten, "Tipping the balance: Allee thresholds, saddle-node bifurcations, and optimal sterile-male release strategies for Anopheles mosquitoes", arXiv:2606.17125, Theorems 3.1–3.4. <https://doi.org/10.48550/arXiv.2606.17125>
