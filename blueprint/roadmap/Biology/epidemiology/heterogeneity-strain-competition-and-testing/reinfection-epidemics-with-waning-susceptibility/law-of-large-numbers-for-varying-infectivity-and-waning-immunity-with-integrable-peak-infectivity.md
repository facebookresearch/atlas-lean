# Law of large numbers for varying infectivity and waning immunity with integrable peak infectivity

**Model.** In a population of size $N$, individual $k$ carries, after its $i$-th infection, an i.i.d. pair of random càdlàg functions $(\lambda_{k,i},\gamma_{k,i})$ of the time since that infection: $\lambda\ge0$ is its infectivity and $\gamma\in[0,1]$ its susceptibility (a different pair $(\lambda_{k,0},\gamma_{k,0})$ describes the initial state, e.g. infected with probability $\bar I(0)$, otherwise fully susceptible). Infectivity and susceptibility do not overlap: $\inf\{t:\gamma(t)>0\}\ge\sup\{t:\lambda(t)>0\}$ a.s. With $\mathcal{A}^N_k(t)$ the age of the current infection and $B^N_k(t)$ the number of infections so far, the normalized force of infection and susceptibility are

$$\bar{\mathfrak{F}}^N(t)=\frac1N\sum_k\lambda_{k,B^N_k(t)}(\mathcal{A}^N_k(t)),\qquad \bar{\mathfrak{S}}^N(t)=\frac1N\sum_k\gamma_{k,B^N_k(t)}(\mathcal{A}^N_k(t)),$$

and individual $k$ is (re)infected at rate $\gamma_{k,B^N_k(t)}(\mathcal{A}^N_k(t))\,\bar{\mathfrak{F}}^N(t)$.

**Assumption.** Only an integrable peak infectivity is required: with $\lambda^*=\sup_t\lambda(t)$ and $\lambda^*_0=\sup_t\lambda_0(t)$,

$$\mathbb{E}[\lambda^*]<\infty,\qquad\mathbb{E}[\lambda_0^*]<\infty$$

(earlier proofs assumed a deterministic bound $\lambda\le\lambda^*$).

**Statement.** As $N\to\infty$, $(\bar{\mathfrak{S}}^N,\bar{\mathfrak{F}}^N)$ converges in probability, locally uniformly in time, to the unique solution of

$$\begin{aligned}
\bar{\mathfrak{S}}(t)&=\mathbb{E}\Big[\gamma_0(t)e^{-\int_0^t\gamma_0(r)\bar{\mathfrak{F}}(r)dr}\Big]+\int_0^t\mathbb{E}\Big[\gamma(t-s)e^{-\int_s^t\gamma(r-s)\bar{\mathfrak{F}}(r)dr}\Big]\bar{\mathfrak{S}}(s)\bar{\mathfrak{F}}(s)\,ds,\\
\bar{\mathfrak{F}}(t)&=\bar\lambda_0(t)+\int_0^t\bar\lambda(t-s)\,\bar{\mathfrak{S}}(s)\bar{\mathfrak{F}}(s)\,ds,
\end{aligned}$$

with $\bar\lambda=\mathbb{E}\lambda$, $\bar\lambda_0=\mathbb{E}\lambda_0$. With constant susceptibility $\gamma\equiv0$ after infection and $\gamma_0\equiv1$ for initially susceptible individuals this reduces to the varying-infectivity SIR model.

## Depends on

- [Law of large numbers for the SI model with varying infectivity on a refining grid](../../stochastic-and-network-epidemic-models/epidemics-on-refining-spatial-grids/law-of-large-numbers-for-the-si-model-with-varying-infectivity-on-a-refining-grid.md)

## Expansion

The rate $\bar{\mathfrak{S}}(s)\bar{\mathfrak{F}}(s)$ is the density of new infections at time $s$. Each such infection starts a fresh infectivity curve, whose mean contribution at time $t$ is $\bar\lambda(t-s)$, giving the renewal equation for $\bar{\mathfrak{F}}$; and a fresh susceptibility curve, which contributes to $\bar{\mathfrak{S}}(t)$ only if the individual has not been reinfected in between, an event of conditional probability $\exp(-\int_s^t\gamma(r-s)\bar{\mathfrak{F}}(r)dr)$. The proof compares the $N$-system with i.i.d. copies driven by the limiting force of infection, constructed on the same Poisson random measures. With unbounded infectivity curves, the error terms are controlled by truncating at a level $M$ and using $\mathbb{E}[\lambda^*\mathbf{1}_{\lambda^*>M}]\to0$, which is where the first-moment assumption enters, together with uniqueness for the limiting system proved by a Gronwall argument.

## Sources

- Raphaël Forien and Étienne Pardoux, "Stochastic epidemic model with varying infectivity and waning immunity: The law of large numbers with unbounded infectivity", Electronic Communications in Probability 31 (2026), 1–13, <https://doi.org/10.1214/26-ecp833>; numbering as in arXiv:2606.11845: Section 2 (model, assumptions (disjoint_support) and (assumption_1st_moment), Theorem 1).
