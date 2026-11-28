# Commuter proportions minimizing the two-patch epidemic threshold

**Setting.** In the two-patch commuter SIR model with permanent residents, fix the home populations $N_i$, transmission rates $\beta_i$ (with $\mathcal R_2=\beta_2/\gamma>\mathcal R_1=\beta_1/\gamma$), recovery rate $\gamma$ and commuting rates $\lambda_i,\mu_i$, and regard the threshold $\mathcal R_{1,2}$ as a function of the numbers of commuters $N_{1c}\in(0,N_1)$, $N_{2c}\in(0,N_2)$. Put $\eta_i=\lambda_i/(\lambda_i+\mu_i)\in(0,1)$, the fraction of time a commuter of patch $i$ spends away, and let $\tilde{\mathcal R}_{1,2}$ be the fast-commuting approximation obtained by setting $\gamma=0$ inside the coefficients $q_{kl}$.

**Proposition (monotonicity).** The map $N_{2c}\mapsto\tilde{\mathcal R}_{1,2}(N_{1c},N_{2c})$ is decreasing for every $N_{1c}$. The map $N_{1c}\mapsto\tilde{\mathcal R}_{1,2}$ is increasing at points where $\eta_2(1-\eta_2)N_{2c}>(1-\eta_1)(N_2-\eta_2N_{2c})$, and the source gives a further sufficient condition for it to be decreasing.

**Proposition (unimodality).** For each $N_{2c}$, the map $N_{1c}\mapsto\tilde{\mathcal R}_{1,2}$ is either decreasing on $(0,N_1)$, or increasing on $(0,N_1)$, or decreasing on $(0,N_{1c}^\star)$ and increasing on $(N_{1c}^\star,N_1)$ for some $N_{1c}^\star$.

**Proposition (trichotomy of the minimizer).** Assume moreover $N_1\mathcal R_2>N_2\mathcal R_1$. If $\gamma$ is small enough compared with the $\lambda_i,\mu_i$, then $(N_{1c},N_{2c})\mapsto\mathcal R_{1,2}$ has a unique minimum at $(N_{1c}^\star,N_{2c}^\star)$ with $N_{2c}^\star=N_2$ (everyone in the high-transmission patch commutes), and:

1. $N_{1c}^\star=0$ if $\eta_2>1-\eta_1$;
2. $N_{1c}^\star=N_1$ if $\eta_1$ and $\eta_2$ are small enough;
3. for suitable $\eta_1,\eta_2$ the minimizer is interior, $N_{1c}^\star\in(0,N_1)$.

## Depends on

- [Reproduction number of the two-patch commuter SIR model](reproduction-number-of-the-two-patch-commuter-sir-model.md)

## Expansion

Write $\tilde{\mathcal R}_{1,2}=\alpha\mathcal R_1+(1-\alpha)\mathcal R_2$ with $\alpha$ the root of the quadratic $P$; lowering the threshold means raising the weight $\alpha$ on the safer patch. Implicit differentiation of $P(\alpha)=0$ gives $\partial\alpha/\partial N_{kc}$ in terms of $\partial q_{12}/\partial N_{kc}$ and $\partial q_{21}/\partial N_{kc}$, whose signs are explicit for $\gamma=0$. At any critical point in $N_{1c}$ one finds $\partial^2\tilde{\mathcal R}_{1,2}/\partial N_{1c}^2>0$, so every critical point is a local minimum and there is at most one, which gives unimodality. Combining the monotonicity in $N_{2c}$ with the boundary behavior in $N_{1c}$ yields the three regimes, and continuity in $\gamma$ transfers them from $\tilde{\mathcal R}_{1,2}$ to $\mathcal R_{1,2}$. The practical reading is that whether residents of the low-transmission patch should commute depends on how long commuters stay away: with long absences ($\eta_2>1-\eta_1$) they should not, with short visits all of them should, and in between a partial commuting share is optimal.

## Sources

- Alain Rapaport, Ismail Mimouni, "The Role of Permanently Resident Populations in the Two-Patches SIR Model with Commuters", Bulletin of Mathematical Biology 85 (2023), 3, <https://doi.org/10.1007/s11538-022-01111-6>. Published version of arXiv:2211.16137, cited next; locators there refer to the arXiv version.
- A. Rapaport and I. Mimouni, "The role of permanently resident populations in the two-patches SIR model with commuters", arXiv:2211.16137 (2022), Section 4 (Propositions 4, 5 and 6), <https://doi.org/10.48550/arXiv.2211.16137>.
