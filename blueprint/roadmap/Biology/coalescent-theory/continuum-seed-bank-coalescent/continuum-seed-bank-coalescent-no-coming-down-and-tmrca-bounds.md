# Continuum seed-bank coalescent: no coming down from infinity and TMRCA bounds

**Model.** Let $\nu$ be a probability measure on $(0,\infty)$, $c > 0$, and $\mu = c\,\nu$. The continuum seed-bank coalescent is a Markov process on partitions whose blocks carry a flag: $0$ (active) or $\lambda \in (0,\infty)$ (dormant, waking at rate $\lambda$). Independently,
- an active block becomes dormant with flag in $B \subset (0,\infty)$ at rate $\mu(B)$;
- a dormant block with flag $\lambda$ becomes active at rate $\lambda$;
- each pair of active blocks merges at rate $1$; dormant blocks never merge.

So each lineage alternates between $\mathrm{Exp}(c)$ active periods and dormant periods with survival function $\int e^{-\lambda t}\nu(d\lambda)$, any completely monotone law (for $\nu = \Gamma(a,b)$ the Lomax law $1 - (1 + t/b)^{-a}$). Let $N_t$ be the number of active blocks and $M_t$ the integer-valued measure recording the flags of dormant blocks, and $T_{MRCA}(n,m) = \inf\{t > 0 : (N_t, M_t) = (1, 0)\}$ from $(N_0, M_0) = (n, m)$.

**Theorem.**
1. *(No coming down from infinity.)* If $N_0 + \|M_0\|_{TV}$ is countably infinite, then almost surely $N_t + \|M_t\|_{TV} = \infty$ for all $t \ge 0$.
2. *(Finite mean TMRCA.)* $\mathbb{E}[T_{MRCA}(n,m)] < \infty$ if and only if the mean dormancy time $\int_{(0,\infty)} \lambda^{-1} \mu(d\lambda)$ is finite.
3. *(Growth of the TMRCA.)* Suppose the flags of the initially dormant blocks are i.i.d. $\nu$. If $\operatorname{supp}\nu \subset (0, \bar\lambda_0]$, then

$$\liminf_{n,\ \|m\|_{TV} \to \infty} \frac{\mathbb{E}[T_{MRCA}(n,m)]}{\log\big(\log n + \|m\|_{TV}/(2c)\big)} \ge \frac{1}{\bar\lambda_0},$$

and for $\nu = \Gamma(a,b)$ the same $\liminf$ is at least $b/a$. If moreover $\operatorname{supp}\nu \subset [\underline\lambda_0, \bar\lambda_0]$ with $\underline\lambda_0 > 0$, the corresponding $\limsup$ is at most $2/\underline\lambda_0$.
4. *(Ancestral line and fixation.)* A single ancestral line has limiting flag law

$$\frac{1}{1 + \int \lambda^{-1}\mu(d\lambda)}\Big(\delta_0 + \lambda^{-1}\mu(d\lambda)\Big),$$

and, when $\int \lambda^{-1}\mu(d\lambda) < \infty$, the dual continuum seed-bank diffusion started from active frequency $x$ and dormant frequency profile $y(\lambda)$ fixes on type $1$ with probability $\big(x + \int y(\lambda)\lambda^{-1}\mu(d\lambda)\big)/\big(1 + \int \lambda^{-1}\mu(d\lambda)\big)$.

## Depends on

- [Seed-bank coalescent](../structured-coalescent/seed-bank-coalescent/seed-bank-coalescent-active-dormant-lineages.md)
- [The seed-bank coalescent does not come down from infinity](../structured-coalescent/seed-bank-coalescent/the-seed-bank-coalescent-does-not-come-down-from.md)

## Expansion

Infinitely many lineages always include infinitely many that fall asleep before they meet anyone, and sleeping blocks cannot merge, so the block count stays infinite. The ancestral line is an alternating renewal process with mean active time $1/c$ and mean dormant time $\int \lambda^{-1}\nu(d\lambda)$, which gives both the limiting flag law and, by the martingale property of the weighted type frequency, the fixation probability. The TMRCA bound comes from the last dormant lineage waking up: the maximum of $\approx \|m\|$ dormancy times with rate at most $\bar\lambda_0$ grows like $\log\|m\|/\bar\lambda_0$, while the Kingman part needs only $O(1)$ time, hence the double-log normalization of the combined count.

## Sources

- Likai Jiao, "Properties of the continuum seed-bank coalescent", arXiv:2402.14149 (2024), Definition 2.1, Theorems 1.1–1.3, Propositions 2.6 and 2.9, <https://doi.org/10.48550/arXiv.2402.14149>.
