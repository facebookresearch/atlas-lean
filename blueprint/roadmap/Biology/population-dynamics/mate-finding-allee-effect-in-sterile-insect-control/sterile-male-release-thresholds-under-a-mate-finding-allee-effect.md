# Sterile-male release thresholds under a mate-finding Allee effect

**Model.** A sex- and stage-structured mosquito model tracks eggs $E$, larvae $L$, pupae $P$, unmated females $F_u$, females mated with wild males $F_{mw}$ or with sterile males $F_{ms}$, wild males $M_w$ and sterile males $M_s$:

$$\begin{aligned}
\dot E &= \phi\Big(1-\tfrac{E}{K_E}\Big)F_{mw} - (\sigma_E+\mu_E)E, &\quad \dot L &= \sigma_E E - (\sigma_L+\mu_L+\delta_L L)L,\\
\dot P &= \sigma_L L - (\sigma_P+\mu_P)P, &\quad \dot F_u &= r\sigma_P P - \frac{M_w+\eta M_s}{\gamma+\zeta(M_w+\eta M_s)}F_u - \mu_F F_u,\\
\dot F_{mw} &= \frac{M_w}{\gamma+\zeta(M_w+\eta M_s)}F_u - \mu_F F_{mw}, &\quad \dot F_{ms} &= \frac{\eta M_s}{\gamma+\zeta(M_w+\eta M_s)}F_u - \mu_F F_{ms},\\
\dot M_w &= (1-r)\sigma_P P - \mu_M M_w, &\quad \dot M_s &= S(t) - \mu_M M_s,
\end{aligned}$$

with nonnegative parameters, positive mortalities, egg capacity $K_E$, larval competition $\delta_L$, mate-search constant $\gamma>0$, refractory period $\zeta$, and sterile-male release rate $S(t)\ge 0$. The Holling type-II mating term vanishes linearly as $M_w\to 0$, producing a mate-finding Allee effect. $\mathcal{R}_0^{q}$ denotes the basic reproduction number of the quick-mate-search model obtained by setting $\gamma=0$.

**Theorem (releases).** Let $S(t) = S_0 + S_1\,(F_u+F_{mw}+F_{ms}+M_w)$ with $S_0, S_1\ge 0$ (constant plus population-responsive release), and let $\mathcal{E}_s$ be the wild-mosquito-free equilibrium.

1. $\mathcal{E}_s$ is locally asymptotically stable for all admissible parameters, and globally asymptotically stable if $\mathcal{R}_0^{q}<1$.
2. If $\mathcal{R}_0^{q}>1$, there are $K_E^{*}, \delta_L^{*}, S_1^{*}>0$ and a continuous $S_0^{*}:[0,S_1^{*}]\to\mathbb{R}$ such that, for $K_E>K_E^{*}$ and $\delta_L<\delta_L^{*}$, the model has exactly two positive equilibria when $0\le S_1\le S_1^{*}$ and $0\le S_0<S_0^{*}(S_1)$; larger releases remove them in a second saddle–node bifurcation.
3. For each initial state $X_0$ in the feasible region there is a constant release $S\equiv S_0>0$ (depending on $X_0$) such that the solution converges to $\mathcal{E}_s$.

## Depends on

- [Allee bistability in a stage-structured mosquito model with Holling type-II mating](allee-bistability-in-a-stage-structured-mosquito-model.md)

## Expansion

Sterile males enter the mating denominator $\gamma+\zeta(M_w+\eta M_s)$ and divert a fraction $\eta M_s/(M_w+\eta M_s)$ of matings to $F_{ms}$; this lowers the effective reproduction curve until the stable and Allee equilibria merge and disappear. Because extinction is locally stable without control, a release only needs to push the state across the Allee separatrix, after which mate-finding failure completes elimination.

## Sources

- A. Gumel, C. A. Safsten, "Tipping the balance: Allee thresholds, saddle-node bifurcations, and optimal sterile-male release strategies for Anopheles mosquitoes", arXiv:2606.17125, Theorems 3.15, 3.16, 3.18 and 3.19. <https://doi.org/10.48550/arXiv.2606.17125>
