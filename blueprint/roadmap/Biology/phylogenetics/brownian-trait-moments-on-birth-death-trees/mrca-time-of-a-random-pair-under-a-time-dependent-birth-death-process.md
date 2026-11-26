# MRCA time of a random pair of extant lineages under a time-dependent birth–death process

**Setting.** A generalized birth–death process starts from one lineage at time $0$, with speciation rate $\lambda(u)$ and extinction rate $\mu(u)$ at time $u$. The probability that a lineage alive at time $s$ has extant descendants at time $t \ge s$ is

$$p(s,t) = \left(1 + \int_s^t e^{-\int_s^u (\lambda(v) - \mu(v))\,dv}\,\mu(u)\,du\right)^{-1},$$

and the reconstructed tree at time $t$ (lineages with descendants at $t$) is a pure-birth process with rate $\tilde\lambda_t(s) = \lambda(s)\,p(s,t)$. Put $\phi_t(s) = \int_0^s \tilde\lambda_t(w)\,dw$. For the tree observed at time $t$, nodes are dated forward from the origin, and $\bar A_t$ is the time of the most recent common ancestor of two lineages sampled uniformly among those extant at $t$.

**Proposition (pure-birth lemma).** For a lineage-homogeneous pure-birth tree with $m$ lineages at time $s$ and $n \ge 2$ at time $t \ge s$,

$$\mathbb{P}\big(\bar A_t \le s \mid m \text{ at } s,\ n \text{ at } t\big) = \Big(1 - \frac{2}{m+1}\Big)\Big(1 + \frac{2}{n-1}\Big).$$

**Theorem.** For $0 < s \le t$, conditional on at least two lineages at $t$,

$$\mathbb{P}\big(\bar A_t \le s \mid \ge 2 \text{ extant at } t\big) = 1 - \frac{2\big(e^{\phi_t(t)} - e^{\phi_t(s)}\big)\big(1 - e^{\phi_t(s)} + \phi_t(s)e^{\phi_t(s)}\big)}{\big(e^{\phi_t(t)} - 1\big)\big(e^{\phi_t(s)} - 1\big)^2},$$

which tends to $0$ as $s \to 0$.

**Corollary (Brownian trait moments).** Let a trait evolve by Brownian motion with variance $\sigma^2$ along the tree. On a fixed ultrametric tree of height $t$ with $n \ge 2$ tips, the expected empirical tip variance is

$$\mathbb{E}\big[\widehat{V}\big] = \sigma^2\Big(t - \frac{2}{n(n-1)}\sum_{i<j} A(i,j)\Big),$$

where $A(i,j)$ is the time of the MRCA of tips $i, j$; as a function of the observation time, the expected empirical variance has slope $\sigma^2$ whenever at least two lineages exist, and the variance of the empirical mean has slope $\sigma^2/n$ while $n$ lineages exist. For a lineage-homogeneous random tree both quantities are therefore linear functionals of the law of $\bar A_t$, which enters them with opposite signs.

## Depends on

- [Generating function of the time-inhomogeneous linear birth–death process](../../population-dynamics/inhomogeneous-sevastyanov-branching-processes/generating-function-of-the-time-inhomogeneous-linear-birth-death-process.md)

## Expansion

The time change $\phi_t$ turns the reconstructed process into a unit-rate Yule process, under which the number of lineages at time $s$ is geometric, $\mathbb{P}(m \text{ at } s) = e^{-\phi_t(s)}(1 - e^{-\phi_t(s)})^{m-1}$, with explicit negative-binomial transitions to time $t$. In a Yule process, two random lineages among $n$ at $t$ descend from distinct ancestors among the $m$ at $s$ with probability given by the Pólya-urn structure of lineage sizes, giving the pure-birth lemma. Averaging it over the joint law of $(m, n)$ and conditioning on $n \ge 2$ gives the closed form. For the trait, the covariance of tips $i, j$ is $\sigma^2 A(i,j)$, and the empirical variance is a quadratic form whose expectation involves only the average pairwise MRCA time.

## Sources

- G. Didier, "Phylogenetic dynamics of MRCA ages and empirical moments of a Brownian trait", arXiv:2605.29736 (2026), Propositions 1–6, <https://doi.org/10.48550/arXiv.2605.29736>.
- T. Stadler, "On incomplete sampling under birth–death models and connections to the sampling-based coalescent", Journal of Theoretical Biology 261 (2009), Theorem 4.1, <https://doi.org/10.1016/j.jtbi.2009.07.018>.
