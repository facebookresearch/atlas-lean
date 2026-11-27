# Kingman limit of the neutral serial-transfer Cannings model

**Neutral serial-transfer model.** Fix $r > 0$ and $\gamma > 1$. Each day starts with $N$ individuals that reproduce by binary splitting at rate $r$ (a Yule process started from $N$). Growth stops at the deterministic time $\sigma$ at which the expected population size reaches $\gamma N$, so the end-of-day size is negative binomial with parameters $N$ and $1/\gamma$. The founders of the next day are a uniform sample of $N$ individuals. Because the daily offspring vectors are i.i.d. and exchangeable with sum $N$, the day-to-day genealogy is a **Cannings model** with days as generations.

**Theorem.** Sample $n$ individuals at day $0$ and let $B^{(N,n)}_g$ be the partition of $\{1,\dots,n\}$ whose blocks group the individuals sharing an ancestor $g$ days earlier. Then for every $n$,

$$\Bigl(B^{(N,n)}_{\lfloor N t / (2(1 - 1/\gamma)) \rfloor}\Bigr)_{t \ge 0} \;\Longrightarrow\; \text{Kingman's } n\text{-coalescent}, \qquad N \to \infty,$$

weakly in the Skorokhod space. Equivalently, the pair-coalescence probability per day is $c_{\gamma,N} \sim 2(1 - 1/\gamma)/N$, and the coalescent effective population size of the experiment is $N_e \sim N/(2(1-1/\gamma))$ days.

## Expansion

By Möhle's criterion it suffices that the probability $c_{\gamma,N}$ that two sampled founders share a parent tends to $0$, and that triple coalescences are of smaller order. If a founder has $G$ end-of-day descendants ($G$ geometric with mean $\gamma$) and $\hat G$ is the size-biased version, then $c_{\gamma,N} \approx (\mathbb E\hat G - 1)/(N\,\mathbb E G) = 2(1 - 1/\gamma)/N$. Multiple mergers are negligible because $G$ has exponential tails. For large $\gamma$, $G/\gamma$ is nearly exponential and $c_{\gamma,N} \sim 2/N$, as in a Moran-type sampling scheme.

## Sources

- Adrián González Casanova, Noemi Kurt, Anton Wakolbinger, Linglong Yuan, "An individual-based model for the Lenski experiment, and the deceleration of the relative fitness", *Stochastic Processes and their Applications* 126 (2016), 2211–2252, <https://doi.org/10.1016/j.spa.2016.01.009>; preprint arXiv:1505.01751, <https://doi.org/10.48550/arXiv.1505.01751>. Numbering of the arXiv version: Definition of the neutral model and sampling rule, Theorem 2.5, proof in Appendix A.
