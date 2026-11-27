# Quasispecies distribution of the sharp-peak Galton–Watson process

Fix a finite alphabet $\mathcal A$ with $\kappa \ge 1$ letters and a sequence length $\ell \ge 1$. Individuals are genotypes $u \in \mathcal A^\ell$. On the **sharp peak landscape** a master sequence $w^*$ has fitness $A(w^*) = \sigma \ge 1$ and every other sequence has fitness $1$. Mutations act independently at each locus: with probability $q \in (0,1)$ a letter is replaced by one of the other $\kappa - 1$ letters chosen uniformly, so the mutation kernel is

$$M(u,v) = \prod_{i=1}^{\ell}\Big((1-q)\mathbf 1_{u(i)=v(i)} + \frac{q}{\kappa-1}\mathbf 1_{u(i)\neq v(i)}\Big).$$

In the multitype Galton–Watson process $(X_n)_{n\ge0}$ on $\mathbb N^{\mathcal A^\ell}$, each individual of type $u$ independently has a Poisson$(A(u))$ number of children, and each child then mutates according to $M$. Write $|X_n|_1$ for the total population size and $\mathcal C_k$ for the set of sequences at Hamming distance $k$ from $w^*$.

**Theorem.** The process survives with positive probability. Conditionally on non-extinction, in the joint limit $\ell \to \infty$, $q \to 0$, $\ell q \to a \in (0,\infty)$:

- if $\sigma e^{-a} \le 1$, then for every $k \ge 0$

$$\lim_{\ell q \to a}\ \lim_{n \to \infty} \frac{1}{|X_n|_1}\sum_{u \in \mathcal C_k} X_n(u) = 0;$$

- if $\sigma e^{-a} > 1$, then for every $k \ge 0$

$$\lim_{\ell q \to a}\ \lim_{n \to \infty} \frac{1}{|X_n|_1}\sum_{u \in \mathcal C_k} X_n(u) = (\sigma e^{-a} - 1)\,\frac{a^k}{k!}\sum_{i \ge 1}\frac{i^k}{\sigma^i}.$$

The limit law on $\{0,1,2,\dots\}$ is the **quasispecies distribution** $\mathcal Q(\sigma,a)$; the condition $\sigma e^{-a} > 1$ is the error threshold, since $e^{-a}$ is the limiting probability that a copy of the master sequence is error-free.

## Expansion

Because the landscape depends only on the Hamming class, the process can be lumped to a Galton–Watson process on classes $0,1,\dots,\ell$. As $n \to \infty$ the class proportions converge to the normalized left Perron–Frobenius eigenvector of the mean matrix; the proof studies this eigenvector through an occupancy process and passes to the long-chain limit. In that limit a class-$0$ individual produces on average $\sigma e^{-a}$ class-$0$ children; class-$k$ offspring of the master are accumulated over the ancestral line, giving the factor $a^k/k!$ weighted by the geometric series $\sum_i i^k \sigma^{-i}$. The resulting distribution coincides with the one obtained for the Moran and Wright–Fisher quasispecies models in the same regime.

## Sources

- Joseba Dalmau, "The distribution of the quasispecies for a Galton–Watson process on the sharp peak landscape", arXiv (2014). Section 2 (model), Section 3 (Theorem 1). <https://doi.org/10.48550/arXiv.1411.4488>. Published version: Journal of Applied Probability 53(2) (2016), 606–613, <https://doi.org/10.1017/jpr.2016.25>; locators above refer to the arXiv version.
