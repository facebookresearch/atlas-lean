# Oldest-allele frequency is Markov in the age-ordered Moran model

**Model.** Fix a population size $n \ge 1$ and a mutation parameter $\theta > 0$. The state is a composition $\sigma = (\sigma_1, \dots, \sigma_k)$ of $n$ (positive integers summing to $n$) listing allele-type counts ordered from youngest (left) to oldest (right). One step of the chain $X_n^{(0,\theta)}$ is an up-step followed by a down-step:
- *up (birth):* a new gene copy joins type $i$ with probability $\sigma_i/(n+\theta)$, or, with probability $\theta/(n+\theta)$, carries a new mutant type placed as the leftmost block, giving $(1, \sigma_1, \dots, \sigma_k)$;
- *down (death):* one of the $n+1$ copies, chosen uniformly (the newborn included), is removed, and an emptied block is deleted.

This is the $(0,\theta)$-ordered Chinese restaurant up-down chain: an infinitely-many-neutral-alleles Moran model that remembers the age order of the types. Let $Z_n^{(0,\theta)}(k)$ be the size of the rightmost block, the number of copies of the **oldest** allele at step $k$.

**Theorem.**
1. If $X_n^{(0,\theta)}$ runs in stationarity, then $Z_n^{(0,\theta)}$ is a time-homogeneous Markov chain on $\{1, \dots, n\}$, including across the steps at which the oldest allele goes extinct and the former second-oldest allele becomes the oldest.
2. With $\alpha_n = (n+\theta)(n+1)$, in stationarity
$$\left(\tfrac{1}{n} Z_n^{(0,\theta)}(\lfloor \alpha_n t \rfloor)\right)_{t \ge 0} \Rightarrow Z^{(0,\theta)}$$
in the Skorokhod topology, where $Z^{(0,\theta)}$ is the diffusion on $[0,1]$ with generator
$$\mathcal{L} f(x) = x(1-x) f''(x) - \theta x f'(x), \qquad x \in (0,1),$$
jumping in from the boundary $0$: a core of its generator is the set of $f \in C^2([0,1])$ with $\int_0^1 (f(x) - f(0))\, \theta (1-x)^{\theta-1}\, dx = 0$ and, if $\theta < 1$, $\lim_{x \to 1} f'(x)(1-x)^\theta = 0$.
3. Started from an empty oldest block, the one-step rescaled jump-in point converges in law to the density $p(x) = \theta(1-x)^{\theta-1}$ on $(0,1)$.

## Expansion

The Markov property comes from an intertwining: with $\Lambda_n$ the stationary conditional law of the full composition given its last block, $\Lambda_n T_n = Q_n \Lambda_n$, so the projection onto the last block is itself Markov. Its kernel is a birth–death kernel for the last block plus, when a last block of size $1$ dies, a regeneration move to the stationary law of the next-oldest block. In the diffusive limit the oldest allele cannot gain by mutation, giving drift $-\theta x$, while neutral resampling gives the Wright–Fisher variance $x(1-x)$; the regeneration law converges to the $\mathrm{Beta}(1,\theta)$ density, the law of a GEM$(\theta)$ stick.

## Sources

- Douglas Rizzolo and Marydol Soto-Santarriaga, "The Oldest Allele in a Moran Model", arXiv:2608.23450 (2026), Section 1.1, Theorems 1–2 and Proposition 5, <https://doi.org/10.48550/arXiv.2608.23450>.
