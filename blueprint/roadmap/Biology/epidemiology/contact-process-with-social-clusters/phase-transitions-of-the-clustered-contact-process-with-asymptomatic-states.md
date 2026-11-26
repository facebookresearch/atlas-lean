# Phase transitions of the spatial clustered contact process with asymptomatic states

**Setting.** Consider the interacting particle system on $\mathbb{Z}^d$ of [the clustered contact process with asymptomatic states](mean-field-survival-criterion-for-pair-clusters-with-asymptomatic-states.md), with cluster size $N$, external rates $\lambda_1,\lambda_2$, internal rates $\phi_1,\phi_2$ and symptom-onset rate $\gamma$, started from a translation-invariant law with positive densities of asymptomatic and symptomatic infected clusters. It *survives* if $\liminf_{t\to\infty} P(\xi_t(x) \ne (0,0)) > 0$ and *dies out* if $\lim_{t\to\infty} P(\xi_t(x) \ne (0,0)) = 0$ for all $x$. Let $\lambda_c$ be the critical value of the basic contact process on $\mathbb{Z}^d$.

**Statement.** Write "(both)" for the condition on both types, "(asymp.)" for the condition on type 1 together with $\gamma < \gamma_-$ for some $\gamma_- > 0$, and "(symp.)" for the condition on type 2 together with $\gamma > \gamma_+$ for some $\gamma_+ < \infty$. Each of the following holds in all three variants.

1. *External rates.* For all $\phi_1,\phi_2 \ge 0$ and all $N$: survival if $\lambda_k > \lambda_c$ (in the "both" variant, $\lambda_1,\lambda_2 > \lambda_+$ for some $\lambda_+ \le \lambda_c$); extinction if $\lambda_k < \lambda_-$ for some $\lambda_- > 0$.
2. *Internal rates.* For every $N > 1$: survival if $\lambda_k > 0$ and $\phi_k > \phi_+$ for some $\phi_+ < \infty$. Extinction if $\lambda_k < \lambda_c$ and $\phi_k < \phi_-$ for some $\phi_- > 0$.
3. *Cluster size.* Survival if $\lambda_k > 0$, $\phi_k > 1$ and $N > N_+$ for some $N_+ < \infty$. Extinction if $\lambda_k < \lambda_c$ and $N < N_-$ for some $N_- > 1$.

So arbitrarily small external infection rates are compatible with survival once clusters are large or internally very infectious, which the basic contact process cannot show.

## Expansion

When both external rates exceed $\lambda_c$ the process dominates a supercritical contact process. When $\gamma$ is small almost every infected individual is asymptomatic and the process is a perturbation of one with only type 1, and symmetrically for $\gamma$ large. Survival for large $\phi$ or large $N$ uses that a cluster with $\phi_k > 1$ (internal growth beating recovery) stays infected for a time that diverges with $\phi$ or with $N$, so even rare external infections accumulate; a block construction compares the rescaled process with supercritical oriented percolation. Extinction for small $\lambda$ uses that every infected cluster heals after an a.s. finite time, and extinction for small $\phi$ or $N$ uses that clusters rarely hold more than one infected individual, so the process is close to a subcritical contact process. The mean-field criterion predicts the same transitions.

## Sources

- K. Belatreche, L. Belhadji and N. Lanchier, The contact process with social clusters and asymptomatic states, arXiv:2610.04323 (2026), Theorems 2–7, <https://doi.org/10.48550/arXiv.2610.04323>.
