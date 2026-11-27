# Mean-field limit of an agent-based SEIR model with individual reproduction numbers

**Model.** A population of $N$ agents evolves in daily steps. Agent $k$ is in a state $z_{k,t}\in\{S,E,I,R\}$ and carries a *personal reproduction number* $x_k$, drawn i.i.d. once from an offspring distribution $X$ with mean $R_0$. Overdispersed $X$ models super-spreaders. Each day:

1. every infected agent contributes $\gamma x_k$ potentially infectious contacts to a global pool, of total size $N_t=\lfloor\gamma\sum_k x_k\mathbf 1[z_{k,t}=I]\rfloor$;
2. $N_t$ agents are drawn uniformly at random, and those that are susceptible become exposed;
3. each exposed agent becomes infected with probability $\sigma$;
4. each infected agent recovers with probability $\gamma$.

Write $(\mathbf s,\mathbf e,\mathbf i,\mathbf r)(t)$ for the population fractions. The comparison model is the discrete-time SEIR recursion with $\alpha=\gamma R_0$:

$$s_{t+1}=s_t-\alpha s_ti_t,\quad e_{t+1}=e_t+\alpha s_ti_t-\sigma e_t,\quad i_{t+1}=i_t+\sigma e_t-\gamma i_t,\quad r_{t+1}=r_t+\gamma i_t .$$

**Theorem.** Assume $X$ has finite variance, fix a horizon $T$, and start from initial fractions converging to $(s_0,e_0,i_0,r_0)$. Then, as $N\to\infty$, $(\mathbf s,\mathbf e,\mathbf i,\mathbf r)(t)$ converges in probability to the deterministic solution $(s_t,e_t,i_t,r_t)$ for every $t\in\{1,\dots,T\}$. The same holds for a second agent-based model in which each susceptible meets at most one infective per day and is infected with probability $\min(\alpha\,\mathbf i(t),1)$, provided $i_t<1/\alpha$ along the deterministic path.

## Proof sketch

The proof is an induction over days using only means and variances. A sequence of uniformly bounded random variables converges in probability to a constant iff its mean converges to that constant and its variance tends to $0$. Given the state at day $t$, the pool size $N_t/N$ is an average of $N\mathbf i(t)$ i.i.d. copies of $\gamma X$, so it concentrates at $\gamma R_0\,\mathbf i(t)=\alpha\mathbf i(t)$ by the law of large numbers. Finite variance is what is needed here. Binomial thinning of exposed and infected agents concentrates as well. Individual heterogeneity therefore averages out, and in a large population super-spreading leaves the epidemic curve unchanged. Its effects show up in finite populations and early on, as a smaller chance of a major outbreak and larger variability of outbreak trajectories. Simulations in the same work show how large $N$ must be before the deterministic curve is a good description when $X$ is highly overdispersed.

## Sources

- François Rousse, Marcus Carlsson, Magnus Ögren and Benjamin Kalischer Wellander, "The role of super-spreaders in modeling of SARS-CoV-2", *Infectious Disease Modelling* 7 (2022), 778–794, <https://doi.org/10.1016/j.idm.2022.10.003>. Preprint version: arXiv:2212.04545 (2022), Section 2 (agent-based model 1), Theorem 3.1 (convergence to discrete SEIR), Theorem 5.1 with Lemmas 5.2, 5.3 and 5.5 and Propositions 5.4 and 5.6 (rigorous statement and proof, including the saturated contact model), <https://doi.org/10.48550/arXiv.2212.04545>.
