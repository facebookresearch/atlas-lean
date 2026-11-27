# Phase diagram of the contact process with an asymptomatic state

**Model.** On $\mathbb{Z}^d$ each site is healthy ($0$), infected asymptomatic ($1$) or infected symptomatic ($2$). With $f_i(x,\xi)$ the fraction of the $2d$ nearest neighbours of $x$ in state $i$, the transitions are

$$0 \to 1 \ \text{at rate}\ \beta_1 f_1(x,\xi) + \beta_2 f_2(x,\xi), \qquad 1 \to 2 \ \text{at rate}\ \gamma, \qquad 1 \to 0 \ \text{and}\ 2 \to 0 \ \text{at rate}\ 1 .$$

New infections are always asymptomatic; asymptomatic and symptomatic individuals infect at rates $\beta_1$ and $\beta_2$ (social distancing or quarantine can make $\beta_2 < \beta_1$). Let $\beta_c \in (0,\infty)$ be the critical infection rate of the basic contact process on $\mathbb{Z}^d$. By monotone coupling with the basic process, $\beta_1, \beta_2 \le \beta_c$ gives extinction and $\beta_1, \beta_2 > \beta_c$ gives survival for every $\gamma$; the cases $\gamma = 0$ and $\gamma = \infty$ reduce to the basic process with rate $\beta_1$ or $\beta_2$.

**Mean-field contrast.** In the homogeneously mixing limit the infection-free state is the only equilibrium unless $\beta_1 + \gamma\beta_2 > 1 + \gamma$, in which case a globally stable endemic equilibrium exists; so without space an epidemic occurs whenever either infection rate is large enough.

**Theorem.** Start with a positive density of infected sites (states $1$ and $2$).
1. If $\beta_1 < \beta_c < \beta_2$: the infection survives locally for all sufficiently large $\gamma < \infty$ and dies out locally for all sufficiently small $\gamma > 0$.
2. If $\beta_2 < \beta_c < \beta_1$: the infection survives locally for all sufficiently small $\gamma > 0$ and dies out locally for all sufficiently large $\gamma < \infty$.
3. If $\beta_1 = 0$ and $\gamma < 1/(4d - 1)$, the infection dies out locally for every $\beta_2 \ge 0$, however large.
4. If $d > 1$, $\beta_2 = 0$ and $\gamma < \infty$, then starting from a single asymptomatic site the infection survives globally with positive probability for all sufficiently large $\beta_1$.

## Proof sketch

Parts 1 and 2 follow by comparing with the basic contact process at the two extreme values of $\gamma$ and using continuity of survival in the parameters via block constructions. Part 3 is the striking spatial effect: when asymptomatic individuals do not transmit, every transmission comes from a symptomatic site, and a newly infected site becomes symptomatic before recovering only with probability $\gamma/(1+\gamma)$. However large $\beta_2$ is, a symptomatic site can only infect its $2d$ neighbours, so the chain of symptomatic sites is dominated by a Galton–Watson branching structure, which is subcritical when $\gamma < 1/(4d-1)$; the infected region then stays bounded in space and time (Lemmas 5–7). Part 4 compares the process with a forest-fire type growth in which infected sites burn through their neighbourhoods before recovering.

## Sources

- Lamia Belhadji, Nicolas Lanchier and Max Mercer, "The contact process with an asymptomatic state", *Stochastic Processes and their Applications* 176 (2024), 104417, <https://doi.org/10.1016/j.spa.2024.104417>. Preprint version: arXiv:2308.00731 (2023), Section 1 (model, mean-field summary) and Theorems 1–4, <https://doi.org/10.48550/arXiv.2308.00731>.
