# Convergence of stochastic growth rate and log-variance under fast-migration aggregation

A population structured into $q$ classes lives on $r$ patches, with state $x(t)\in\mathbb R_+^{qr}$. A Markov environment $\tau_t\in\{1,\dots,n\}$ selects, for each time step, a demographic matrix and a migration matrix. Within one demographic step there are $k$ fast migration steps, and $H_{k,\eta}$ is the resulting one-step projection matrix in environment $\eta$. In the classical model, demography follows $k$ migrations. In the re-scaled model, survival acts on the fast scale: each migration step is accompanied by a survival factor whose $k$-fold product gives the slow survival, $H_{k,\eta}=\tilde D_\eta(S_{k,\eta}P_\eta)^k$.

**Hypotheses.** (H1) $H_{k,\eta}\to\bar H_\eta$ as $k\to\infty$. (H2) $\bar H_\eta=D_\eta G$ with $G\in\mathbb R_+^{q\times qr}$ independent of $\eta$. (H3) each $D_\eta$ is row-allowable and $G$ column-allowable. The aggregated variables $y=Gx$ (class totals) then follow the reduced system $y(t+1)=GD_{\tau_{t+1}}y(t)$.

**Theorem.** Let $\tau_t$ be an irreducible, aperiodic homogeneous Markov chain and assume (H1)–(H3). If the aggregated set $\mathcal A_{ag}=\{GD_\eta\}$ is ergodic (some fixed-length product of its matrices is always positive), then the original sets $\{H_{k,\eta}\}_\eta$ are ergodic for all large $k$. The stochastic growth rate $\log\lambda_S=\lim_t t^{-1}\log\|x(t)\|$ and the scaled logarithmic variance $\sigma^2=\lim_t t^{-1}\mathrm{Var}\log\|x(t)\|$ therefore exist, and

$$
\lim_{k\to\infty}\lambda_{S,k}=\hat\lambda_S,\qquad \lim_{k\to\infty}\sigma_k=\hat\sigma,
$$

where $\hat\lambda_S,\hat\sigma$ are those of the reduced system. The asymptotically lognormal law of total population size can thus be computed from the $q$-dimensional reduced model.

In the re-scaled survival model, the per-class limit of $(S_{k,\eta}P_\eta)^k$ is $\gamma^i_\eta v^i_\eta\mathbf 1^\top$. Here $v^i_\eta$ is the stationary migration distribution of class $i$, and $\gamma^i_\eta=\exp(\sum_\alpha v^{i,\alpha}_\eta\log s^{i,\alpha}_\eta)$ is the geometric mean of the patch survivals weighted by $v^i_\eta$. The reduced system therefore uses this geometric-mean survival rather than the arithmetic mean that arises when survival acts after migration.

## Proof sketch

Ergodicity of products of nonnegative matrices (the Furstenberg–Kesten and Cohen theory) gives existence of $\lambda_S$ and $\sigma^2$ and a central limit theorem for $\log\|x(t)\|$. Because $H_{k,\eta}\to D_\eta G$, products of the original matrices factor approximately through $G$. Continuity of the Lyapunov exponent and of the variance on ergodic sets then passes the limits to the reduced system. Survival applied at each fast step makes the limit a product of $s^{v}$ terms, which is where the geometric mean comes from.

## Related topics

- [Matrix population models](../../../matrix-population-models/README.md)

## Sources

- Luis Sanz and Rafael Bravo de la Parra, "Stochastic matrix metapopulation models with fast migration: Re-scaling survival to the fast scale", *Ecological Modelling* 418 (2020), 108829, <https://doi.org/10.1016/j.ecolmodel.2019.108829>. Preprint version: arXiv:2402.03888 (2024), Section 2 (re-scaled model and reduced system (modagreg3)), Appendix A (Theorem 1), Appendix B (Hypotheses 1–3, Proposition 2, Theorem 3), <https://doi.org/10.48550/arXiv.2402.03888>.
