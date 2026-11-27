# Diffusion limit of the two-size Wright-Fisher model

**Setting.** A haploid population has type-0 (small) and type-1 (large) individuals. Each generation has a resource budget $R>0$; placing a type-0 offspring in the next generation costs $\vartheta\in(0,1)$ units and a type-1 offspring costs $1$. If the current proportion of type 0 is $x$, offspring are created one at a time, each independently of type $0$ with probability $\rho_R(x)$ and of type 1 otherwise (for example $\rho_R(x)=s_R(x)(1-\beta_{1,R})+(1-s_R(x))\beta_{0,R}$ with frequency-dependent selection $s_R$ and parent-independent mutation probabilities $\beta_{i,R}$), until the accumulated cost first reaches or exceeds $R$. The next generation consists of the offspring created so far, so the population size $M^R_n$ is random. Let $X^R_n$ be the proportion of type 0 in generation $n$.

**Theorem 2.1 (diffusion limit).** Let $\rho:[0,1]\to\mathbb R$ be Lipschitz continuous. Suppose $X^R_0\to x_0\in[0,1]$ in probability and $R(\rho_R(x)-x)\to\rho(x)$ uniformly in $x\in[0,1]$ as $R\to\infty$. Then $(X^R_{\lfloor Rt\rfloor})_{t\ge0}$ converges in distribution to the solution of

$$dX_t=\bigl(-(1-\vartheta)X_t(1-X_t)+\rho(X_t)\bigr)\,dt+\sqrt{X_t(1-X_t)\bigl(1-(1-\vartheta)X_t\bigr)}\,dB_t,\qquad X_0=x_0,$$

with $B$ a standard Brownian motion.

**Theorem 2.2 (model variant).** In the variant in which reproduction stops at the last offspring that still fits in the budget (so the cost never exceeds $R$), the same scaling gives the limit $dX_t=\rho(X_t)\,dt+\sqrt{X_t(1-X_t)(1-(1-\vartheta)X_t)}\,dB_t$, without the $-(1-\vartheta)X_t(1-X_t)$ drift.

## Proof idea

The sequential sampling is a renewal process: the cost increments are i.i.d., equal to $\vartheta$ with probability $p=\rho_R(x)$ and to $1$ otherwise, with mean $\mu(p)=1-(1-\vartheta)p$, and the generation size is the first passage time $\tau(R)$ of the cost walk above $R$, about $R/\mu(p)$. The new type-0 proportion is the fraction of $\vartheta$-steps among the first $\tau(R)$ steps. Its conditional mean differs from $p$ at order $1/R$ because of the overshoot: the final, stopping step is size-biased towards the larger cost $1$, so the last individual is more likely to be type 1, which produces the drift $-(1-\vartheta)x(1-x)$ that favours large individuals even under neutrality ($\rho\equiv0$). The variance is $p(1-p)/\tau(R)\approx p(1-p)\mu(p)/R$, giving the diffusion coefficient $x(1-x)(1-(1-\vartheta)x)$: smaller individuals are more numerous, so drift is weaker when they are common. The proof needs renewal theorems (distribution of the stopping summand, $L^p$-convergence of $R/\tau(R)$) holding uniformly in $p\in[0,1]$ (Propositions 3.1 and 3.6). In the variant the overshoot step is discarded, removing the bias.

## Sources

- G. Alsmeyer, F. Cordero and H. Dopmeyer, "A two-size Wright–Fisher model: asymptotic analysis via uniform renewal theory", Stochastic Processes and their Applications 192 (2026), 104812, <https://doi.org/10.1016/j.spa.2025.104812>. Numbering as in the preprint arXiv:2502.03056v2, <https://arxiv.org/abs/2502.03056v2>: Theorem 2.1, Theorem 2.2, Proposition 3.1, Proposition 3.6, Proposition 4.1.
