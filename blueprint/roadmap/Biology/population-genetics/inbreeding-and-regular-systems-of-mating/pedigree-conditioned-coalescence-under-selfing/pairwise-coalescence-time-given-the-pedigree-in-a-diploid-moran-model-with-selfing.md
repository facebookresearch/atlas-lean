# Pairwise coalescence time given the pedigree in a diploid Moran model with selfing

**Model.** A diploid, monoecious, panmictic population has constant size $N$ and overlapping generations. At each time step one uniformly chosen individual dies and is replaced by an offspring that, with probability $1 - \alpha_N$, is produced by outcrossing (two distinct parents chosen uniformly from the previous step, one gene copy from each by Mendel's laws) and, with probability $\alpha_N$, by selfing (one uniformly chosen parent transmits each of the offspring's two copies independently and uniformly from its own two). The record of all parent–offspring relations is the population pedigree, with $\sigma$-algebra $\mathcal{A}_N$. Sample two gene copies, either in two **different** individuals ($\mathbb{P}_{\mathrm{diff}}$) or in the **same** individual ($\mathbb{P}_{\mathrm{same}}$), and let $\tau^{(N)}$ be the number of steps back until they coalesce.

**Theorem (unconditional law).** If $\alpha_N \to \alpha \in [0,1]$, then for $t \ge 0$

$$\mathbb{P}_{\mathrm{diff}}\big(N^{-2}\tau^{(N)} > t\big) \to e^{-\frac{2}{2-\alpha}t}, \qquad \mathbb{P}_{\mathrm{same}}\big(N^{-2}\tau^{(N)} > t\big) \to \frac{2-2\alpha}{2-\alpha}\,e^{-\frac{2}{2-\alpha}t}.$$

Selfing speeds coalescence by the classical factor $\frac{2}{2-\alpha} = 1 + F$, with $F = \alpha/(2-\alpha)$ the equilibrium inbreeding coefficient; two copies in one individual coalesce almost instantly with probability $F$.

**Theorem (conditional on the pedigree, different individuals).** For every $t \ge 0$, as $N \to \infty$, in distribution:
- if $N(1 - \alpha_N) \to \infty$ and $\alpha_N \to \alpha$, then $\mathbb{P}_{\mathrm{diff}}(N^{-2}\tau^{(N)} > t \mid \mathcal{A}_N) \to e^{-\frac{2}{2-\alpha}t}$ (the pedigree does not matter; the convergence holds in $L^2$);
- if $N(1-\alpha_N) \to \lambda \in [0,\infty)$, with on average $\lambda$ outcrossing events per $N$ steps, the conditional survival function converges to a nondegenerate random limit $\mathbb{P}(T_\lambda > t \mid G_\lambda)$ determined by a random ancestral graph $G_\lambda$; for $\lambda = 0$ the limit is the Bernoulli variable $\mathbf{1}\{\mathrm{Exp}(2) > t\}$.

In the critical regime the pedigree's influence is quantified exactly:

$$\mathrm{Var}\big(\mathbb{E}[T_\lambda \mid G_\lambda]\big) = \mathrm{Cov}(T_\lambda, T'_\lambda) = \frac{1}{2}\cdot\frac{\lambda + 36}{\lambda^2 + 26\lambda + 72},$$

where $T_\lambda, T'_\lambda$ are coalescence times at two loci sharing the pedigree; this equals $\mathbb{E}\int_0^\infty \big(\mathbb{P}(T_\lambda > t \mid G_\lambda) - e^{-2t}\big)^2 dt$ and behaves as $\frac14 - \frac{\lambda}{12}$ as $\lambda \to 0$ and $\frac{1}{2\lambda}$ as $\lambda \to \infty$.

**Theorem (conditional, same individual).** If $\alpha_N \to \alpha$, then $\mathbb{P}_{\mathrm{same}}(N^{-2}\tau^{(N)} > t \mid \mathcal{A}_N)$ converges in distribution to $e^{-t}$ if $\alpha = 0$, to $2^{-U} e^{-\frac{2}{2-\alpha}t}$ with $\mathbb{P}(U = k) = \alpha^k(1-\alpha)$ if $\alpha \in (0,1)$, and to $0$ if $\alpha = 1$.

## Expansion

Tracing two copies back, each step either hits their current host individuals (probability of order $1/N$) or not. A run of selfing ancestors of the shared individual gives each step a chance $1/2$ to coalesce; $U$ is the number of consecutive selfing generations in the pedigree above the sampled individual, so given the pedigree the probability of escaping that run is $2^{-U}$. When outcrossing is common, the two copies quickly separate into distinct individuals, after which the pedigree averages out (a law of large numbers over many independent pedigree branches) and the exponential rate $2/(2-\alpha)$ emerges. When outcrossing is rare on the $N^2$ coalescent scale, the few outcrossing events form a finite random graph that the limit remembers, so coalescence times at different loci stay correlated.

## Sources

- Maximillian Newman, John Wakeley and Wai-Tong Louis Fan, "Conditional gene genealogies given the population pedigree for a diploid Moran model with selfing", Theor. Popul. Biol. 165 (2025), 29–44, <https://doi.org/10.1016/j.tpb.2025.05.003>. Numbering follows the arXiv version, arXiv:2411.13048 (2024): Section 2, Theorems 3.1, 4.1 and 4.5, Propositions 5.4 and 5.6, Theorem 7.18, <https://doi.org/10.48550/arXiv.2411.13048>.
