# Expected state-deviation correlation under an indel process

**Model (two-state substitution–insertion–deletion process on a tree).** Each edge $e=(u,v)$ of a rooted binary tree carries a length $t_e>0$, a substitution rate $\nu_e$, a deletion rate $\mu_e$ and an insertion rate $\lambda_e$. The sequence at $v$ is obtained from the binary sequence at $u$ by running, for time $t_e$, the following continuous-time process: every present site flips its state at rate $\nu_e$ and is deleted at rate $\mu_e$, and each present site gives birth, at rate $\lambda_e$, to a new site with a uniformly random state immediately to its right (insertions are per present site, so an empty sequence stays empty). The root sequence is i.i.d. uniform on $\{0,1\}$. Unlike the TKF91 model there is no immortal link and no stationarity assumption on the length.

For a node $u$ let $K_u$ be the length of its sequence, $Z_u$ the number of zeros, and define the **state deviation**

$$\Delta_u = Z_u - \tfrac{1}{2}K_u .$$

For two leaves $a,b$ the alignment-free statistic is the product $D(a,b)=\Delta_a\Delta_b$.

**Moments of the length process.** On a single edge with parameters $(t;\nu,\mu,\lambda)$ and $\mu\neq\lambda$, the descendants of one ancestral site form a linear birth–death process, so

$$\mathbb{E}[K_a \mid K_r = 1] = e^{-(\mu-\lambda)t}, \qquad \operatorname{Var}[K_a \mid K_r = 1] = \frac{\mu+\lambda}{\mu-\lambda}\left(e^{-(\mu-\lambda)t}-e^{-2(\mu-\lambda)t}\right).$$

**Lemma (single channel).** On an edge from $r$ to $a$,

$$\mathbb{E}[\Delta_a \mid K_r, Z_r] = e^{-(2\nu+\mu)t}\,\Delta_r .$$

**Lemma (fork channel).** For a root $r$ with sequence length $k_r$, an edge $e_u=(r,u)$ and two child edges $e_a=(u,a)$, $e_b=(u,b)$,

$$\mathbb{E}[D(a,b)] = e^{-(2\nu_a+\mu_a)t_a}\,e^{-(2\nu_b+\mu_b)t_b}\,e^{-(\mu_u-\lambda_u)t_u}\,\frac{k_r}{4}.$$

**Lemma (molecular clock).** If all edges share $(\nu,\mu,\lambda)$, the leaves are contemporaneous with $t=t_a=t_b$, and $\kappa = k_r e^{-(\mu-\lambda)(t_u+t)}/4$, then

$$\mathbb{E}[D(a,b)] = e^{-(4\nu+\mu+\lambda)t}\,\kappa .$$

Hence $-2\log\mathbb{E}[\kappa^{-1}D(a,b)] = 2\beta t$ with $\beta = 4\nu+\mu+\lambda$: the quantity $D^*(a,b) = -2\log(\kappa^{-1}D(a,b))$ estimates an additive tree metric with edge weights $\beta t_e$, so a distance-based method can recover the tree without aligning the sequences.

## Expansion

A surviving ancestral site keeps its state with probability $1-p$ where $p=(1-e^{-2\nu t})/2$, and survives with probability $e^{-\mu t}$; an inserted site is uniform at the end of the edge, so it contributes nothing to the conditional mean of $\Delta_a$. Writing $\mathbb{E}[Z_a\mid K_r,Z_r]$ as surviving zeros plus surviving flipped ones plus half the new sites, and subtracting half of $\mathbb{E}[K_a\mid K_r]=K_re^{-(\mu-\lambda)t}$, leaves $(1-2p)e^{-\mu t}\Delta_r = e^{-(2\nu+\mu)t}\Delta_r$. For the fork, the Markov property makes $\Delta_a$ and $\Delta_b$ conditionally independent given the sequence at $u$, so $\mathbb{E}[D(a,b)]$ is the product of the two decay factors times $\mathbb{E}[\Delta_u^2] = \mathbb{E}[K_u]/4$, because $Z_u$ given $K_u$ is binomial with parameter $1/2$. The statistic uses only state counts, so it needs no homology assignment; applying it to matched blocks of length about $k^{\zeta}$ ($\zeta>1/2$) gives the estimator used for reconstruction.

## Sources

- Constantinos Daskalakis and Sebastien Roch, "Alignment-free phylogenetic reconstruction: sample complexity via a branching process analysis", arXiv:1109.5002 (2011), Section 1.1 (Definitions 1.1 and 1.3–1.5), Section 2.2 (Lemmas 2.2–2.4 and the moment formulas preceding them), <https://doi.org/10.48550/arXiv.1109.5002>. Published version: The Annals of Applied Probability 23(2) (2013), 693–721, <https://doi.org/10.1214/12-aap852>; locators above refer to the arXiv version.
