# Two phase transitions in the symptom-onset rate for a clustered contact process

**Model.** Each site of $\mathbb Z^d$ holds a social cluster of $N$ individuals, each healthy, asymptomatic infected (state 1) or symptomatic infected (state 2). Newly infected individuals are asymptomatic and become symptomatic at rate $\gamma$ (the "mutation" rate); every infected individual recovers at rate $1$. An individual in state $i$ infects individuals in adjacent clusters at external rate $\lambda_i$ and individuals in its own cluster at internal rate $\phi_i$. With $N = 1$ and a single infected state this is the contact process, with critical value $\lambda_c$.

**Theorem.** Suppose either
- (A) asymptomatics spread only externally and subcritically, symptomatics only internally and strongly: $\lambda_1 \in (0, \lambda_c)$, $\lambda_2 = 0$, $\phi_1 = 0$, $\phi_2 = N$; or
- (B) the reverse: $\lambda_1 = 0$, $\lambda_2 \in (0, \lambda_c)$, $\phi_1 = N$, $\phi_2 = 0$.

Then (a) for every $N > 1$ there are $0 < \gamma_- < \gamma_+ < \infty$ such that the epidemic goes extinct whenever $\gamma \notin (\gamma_-, \gamma_+)$; and (b) for every $\gamma \in (0, \infty)$ there is $N_+ < \infty$ such that the epidemic survives for all $N > N_+$. Hence for large clusters there are at least two phase transitions in $\gamma$: extinction for extreme symptom-onset rates, survival for intermediate ones.

In the mean-field model with clusters of size two, case (A) survives iff $-\gamma^2 + (\lambda_1(1 + \phi_2) - 3)\gamma + (\lambda_1 - 1)(2 + \phi_2) > 0$; for $\lambda_1 = 3/4$, $\phi_2 = 11$ this gives survival exactly for $3 - \sqrt{23}/2 < \gamma < 3 + \sqrt{23}/2$.

## Expansion

In case (A), if $\gamma$ is very small, infected individuals stay asymptomatic and the process is dominated by a subcritical contact process between clusters, so it dies out; if $\gamma$ is very large, individuals become symptomatic almost immediately and can no longer reach neighbouring clusters, so the infection is confined to one cluster and dies out. For intermediate $\gamma$ and large $N$, a symptomatic individual ignites an outbreak inside its cluster that lasts long and produces many asymptomatic individuals, each of which has a fixed chance of seeding a neighbouring cluster before turning symptomatic; a block construction compares clusters with supercritical oriented site percolation. Survival is thus not monotone in $\gamma$, unlike in the infection rates.

## Sources

- L. Belhadji and N. Lanchier, "Multiple transition points for an epidemic model", arXiv:2611.23569 (2026), Theorems 1–2 and the mean-field analysis in Section 1, <https://doi.org/10.48550/arXiv.2611.23569>.
