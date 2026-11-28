# Almost-sure limit of the allelic frequency spectrum of a splitting tree

**Setting.** A *splitting tree* is a binary homogeneous Crump–Mode–Jagers population: individuals have i.i.d. lifetimes with arbitrary law $\mathbb{P}_V$ on $(0,\infty]$ and give birth to single offspring at the times of a Poisson process of rate $b$ during their lives. Let $N_t$ be the number of individuals alive at time $t$ and $W(t) = \mathbb{E}[N_t \mid N_t > 0]$ (the *scale function*). Its Laplace transform is $\int_0^\infty W(s)e^{-\lambda s}\,ds = 1/\psi(\lambda)$ for $\lambda > \alpha$, where

$$\psi(x) = x - \int_{(0,\infty]} \big(1 - e^{-rx}\big)\, b\,\mathbb{P}_V(dr),$$

and the Malthusian parameter $\alpha$ is the largest root of $\psi$. Assume the supercritical case $\alpha > 0$, equivalently $b\,\mathbb{E}[V] > 1$, and write $\mathbb{P}_\infty$ for the law conditioned on non-extinction.

Neutral mutations hit each individual at the times of an independent Poisson process of rate $\theta > 0$ under the infinitely-many-alleles model, and types are inherited. The **allelic frequency spectrum** $A(k,t)$ is the number of distinct alleles (families) carried by exactly $k$ individuals alive at time $t$. Cutting every branch at mutations gives the *clonal* splitting tree, with Laplace exponent $\psi_\theta(x) = x\,\psi(x+\theta)/(x+\theta)$ and scale function $W_\theta$.

**Theorem.** There is a random variable $\mathcal{E}$, exponentially distributed with parameter $1$ under $\mathbb{P}_\infty$, such that

$$\lim_{t\to\infty} e^{-\alpha t} N_t = \frac{\mathcal{E}}{\psi'(\alpha)} \quad \text{a.s. and in } L^2,$$

and for every $k \ge 1$

$$\lim_{t\to\infty} e^{-\alpha t} A(k,t) = \frac{c_k\,\mathcal{E}}{\psi'(\alpha)} \quad \text{a.s. and in } L^2, \qquad c_k = \int_0^\infty \frac{\theta e^{-\theta a}}{W_\theta(a)^{2}}\Big(1 - \frac{1}{W_\theta(a)}\Big)^{k-1} da.$$

So the number $A(k,t)/N_t$ of size-$k$ families per individual converges almost surely on survival to the deterministic constant $c_k$.

**Scale-function asymptotics.** $e^{-\alpha t}\psi'(\alpha)W(t) - 1 = O(e^{-\gamma t})$ for some $\gamma > 0$. For the clonal tree: if $\theta < \alpha$ (clonal supercritical) $W_\theta(t) \sim e^{(\alpha-\theta)t}/\psi_\theta(\alpha-\theta)$; if $\theta > \alpha$ (clonal subcritical) $W_\theta(t) = \theta/\psi(\theta) + O(e^{-(\theta-\alpha)t})$; if $\theta = \alpha$, $W_\theta(t) \sim \theta t/\psi'(\alpha)$.

## Expansion

Conditionally on survival to time $t$, the genealogy of the living individuals is a coalescent point process: i.i.d. node depths $H_i$ with $\mathbb{P}(H_1 > s) = 1/W(s)$, stopped at the first value exceeding $t$, so $N_t$ is geometric with parameter $1/W(t)$. A family born by a mutation at age $a$ before $t$ survives to time $t$ with probability $1/W_\theta(a)$ and, given survival, has geometric size with parameter $1/W_\theta(a)$; the product $W_\theta(a)^{-1}\cdot W_\theta(a)^{-1}(1-W_\theta(a)^{-1})^{k-1}$ is the integrand of $c_k$, the extra factor $1/W_\theta(a)$ being the survival probability of the family. Consistently, $\sum_k k\,c_k=\int_0^\infty\theta e^{-\theta a}\,da=1$, matching $\sum_k kA(k,t)=N_t$; the weight $\theta e^{-\theta a}$ is the rate at which surviving lineages carry their most recent mutation at age $a$. Since $A(k,t)$ is a general branching process counted with a random characteristic, the Nerman-type law of large numbers gives convergence to the same martingale limit $\mathcal{E}$ as $N_t$.

## Sources

- Benoit Henry, "Approximation of the allelic frequency spectrum in general supercritical branching populations", *Stochastic Process. Appl.* 132 (2021), 192-225. <https://doi.org/10.1016/j.spa.2020.10.008>
- Preprint version (the locators in this item follow its numbering): Benoit Henry, "Approximations of the allelic frequency spectrum in general supercritical branching populations", arXiv:1701.07281 (2017), Section 2 (Lemmas 2.2–2.3, Theorems 2.4–2.5, quoting Champagnat and Lambert, "Splitting trees with neutral Poissonian mutations I: Small families"), <https://doi.org/10.48550/arXiv.1701.07281>. The preprint's display (2.13) of $c_k$ drops the square on $W_\theta(a)$; its expectation formula (2.11), covariance (3.1) and Section 4, as well as Champagnat and Lambert (arXiv:1009.0680, Proposition 5.1), all carry $W_\theta^{-2}$, which is used above.
