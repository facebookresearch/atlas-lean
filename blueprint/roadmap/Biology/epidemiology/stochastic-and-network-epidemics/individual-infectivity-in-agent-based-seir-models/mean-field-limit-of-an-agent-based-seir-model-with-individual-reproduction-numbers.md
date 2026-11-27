# Mean-field limit of an agent-based SEIR model with individual reproduction numbers

**Model.** A population of $N$ agents evolves in daily steps. Agent $k$ is in a state $z_{k,t}\in\{S,E,I,R\}$ and carries a *personal reproduction number* $x_k$, drawn i.i.d. once from an offspring distribution $X$ with mean $R_0$. Overdispersed $X$ models super-spreaders. Each day:

1. every infected agent contributes $\gamma x_k$ potentially infectious contacts to a global pool, of total size $N_t=\min\big(\lfloor\gamma\sum_k x_k\mathbf 1[z_{k,t}=I]\rfloor,\,N\big)$ (the pool is capped at $N$, so that the next step is defined);
2. $N_t$ agents are drawn uniformly at random, and those that are susceptible become exposed;
3. each exposed agent becomes infected with probability $\sigma$;
4. each infected agent recovers with probability $\gamma$.

Write $(\mathbf s,\mathbf e,\mathbf i,\mathbf r)(t)$ for the population fractions. The comparison model is the discrete-time SEIR recursion with $\alpha=\gamma R_0$:

$$s_{t+1}=s_t-\alpha s_ti_t,\quad e_{t+1}=e_t+\alpha s_ti_t-\sigma e_t,\quad i_{t+1}=i_t+\sigma e_t-\gamma i_t,\quad r_{t+1}=r_t+\gamma i_t .$$

**Theorem.** Assume $X$ has finite variance, fix $\varepsilon\in(0,1)$ and a horizon $T\in\mathbb N$, and start the agent-based model with $\lfloor\varepsilon N\rfloor$ infected agents chosen uniformly at random and all other agents susceptible; start the recursion at $(s_0,e_0,i_0,r_0)=(1-\varepsilon,0,\varepsilon,0)$. Assume $i_t<1/\alpha$ for all $t\in\{0,\dots,T\}$ along the deterministic path. Then, as $N\to\infty$, $(\mathbf s,\mathbf e,\mathbf i,\mathbf r)(t)$ converges in probability to $(s_t,e_t,i_t,r_t)$ for every $t\in\{1,\dots,T\}$: for every $\delta>0$ the probability that all four fractions are within $\delta$ of the recursion for all $t\in\{1,\dots,T\}$ tends to $1$.

## Proof sketch

The proof is an induction over days using only means and variances. A sequence of uniformly bounded random variables converges in probability to a constant iff its mean converges to that constant and its variance tends to $0$. Given the state at day $t$, the uncapped pool size divided by $N$ is an average of $N\mathbf i(t)$ i.i.d. copies of $\gamma X$, so it concentrates at $\gamma R_0\,\mathbf i(t)=\alpha\mathbf i(t)$ by the law of large numbers, and the capped fraction $N_t/N$ concentrates at $\min(\alpha\mathbf i(t),1)$. The hypothesis $i_t<1/\alpha$ keeps this below $1$, so the cap is inactive in the limit and $s_{t+1}=s_t(1-\alpha i_t)\ge0$; without it the recursion leaves $[0,1]$ (for $\gamma=\sigma=1$, $X\equiv4$ and $(s_0,i_0)=(\tfrac12,\tfrac12)$ it gives $s_1=-\tfrac12$). Finite variance is what is needed here. Binomial thinning of exposed and infected agents concentrates as well. Individual heterogeneity therefore averages out, and in a large population super-spreading leaves the epidemic curve unchanged. Its effects show up in finite populations and early on, as a smaller chance of a major outbreak and larger variability of outbreak trajectories. Simulations in the same work show how large $N$ must be before the deterministic curve is a good description when $X$ is highly overdispersed.

## Sources

- François Rousse, Marcus Carlsson, Magnus Ögren and Benjamin Kalischer Wellander, "The role of super-spreaders in modeling of SARS-CoV-2", *Infectious Disease Modelling* 7 (2022), 778–794, <https://doi.org/10.1016/j.idm.2022.10.003>. Preprint version: arXiv:2212.04545 (2022), Section 2 (agent-based model 1), Theorem 3.1 (convergence to discrete SEIR), Theorem 5.1 with Lemmas 5.2, 5.3 and 5.5 and Propositions 5.4 and 5.6 (rigorous statement and proof for AB-model 1 with the pool capped at $N$, under $i_d(t)<1/\alpha$), <https://doi.org/10.48550/arXiv.2212.04545>.
