# Limit law of an external branch length in the Beta-coalescent

Let $\Pi^{(n)}$ be a $\Lambda$-$n$-coalescent whose measure satisfies $\rho(t)=\int_t^1x^{-2}\Lambda(dx)=C_0t^{-\alpha}+O(t^{-\alpha+\zeta})$ as $t\to0$, with $C_0>0$, $\alpha\in(1,2)$, $\zeta>1-1/\alpha$ (for instance the $\mathrm{Beta}(2-\alpha,\alpha)$-coalescent). By exchangeability, follow individual $1$ and define

- $T^{(n)}=\inf\{t:\{1\}\notin\Pi^{(n)}_t\}$, the length of a random external branch;
- $\sigma^{(n)}=\inf\{k:\{1\}\notin\pi_k\}$, the number of collisions up to and including the one ending that branch, where $\pi_k$ is the state after $k$ jumps;
- $\tau^{(n)}$, the total number of collisions until the most recent common ancestor.

**Theorem (collision count).** As $n\to\infty$,

$$
\frac{\sigma^{(n)}}{n(\alpha-1)}\xrightarrow{d}\sigma,\qquad \frac{\sigma^{(n)}}{\tau^{(n)}}\xrightarrow{d}\sigma,\qquad \sigma\sim\mathrm{Beta}(1,\alpha).
$$

**Theorem (branch length).** As $n\to\infty$,

$$
n^{\alpha-1}T^{(n)}\xrightarrow{d}T=\frac{1}{C_0\Gamma(2-\alpha)}\big((1-\sigma)^{1-\alpha}-1\big),
$$

and $T$ has density

$$
f_T(t)=\frac{\alpha\,C_0\Gamma(2-\alpha)}{\alpha-1}\big(1+C_0\Gamma(2-\alpha)\,t\big)^{-\frac{\alpha}{\alpha-1}-1},\qquad t\ge0 .
$$

For the $\mathrm{Beta}(2-\alpha,\alpha)$-coalescent this is $f_T(t)=\frac{1}{(\alpha-1)\Gamma(\alpha)}\big(1+\frac{t}{\alpha\Gamma(\alpha)}\big)^{-\frac{\alpha}{\alpha-1}-1}$.

**Corollary.** The number of blocks present when the chosen branch ends satisfies $n^{-1}R^{(n)}_{T^{(n)}}\xrightarrow{d}1-\sigma$, a law with density $\alpha x^{\alpha-1}$ on $[0,1]$.

The scaling $n^{\alpha-1}$ interpolates between Kingman's coalescent, where $nT^{(n)}$ has limit density $8/(2+t)^3$ and $\sigma^{(n)}/n\to\mathrm{Beta}(1,2)$, and the Bolthausen–Sznitman coalescent ($\alpha=1$), where $\log(n)\,T^{(n)}\to\mathrm{Exp}(1)$.

## Depends on

- [Small-time law of large numbers for the Beta-coalescent block-counting process](small-time-law-of-large-numbers-for-the-beta-coalescent-block-counting-process.md)

## Expansion

At a collision with $b$ blocks that loses $X+1$ of them, the chosen singleton is involved with probability $(X+1)/b$. Since a collision removes on average $1/(\alpha-1)$ blocks, after $\lfloor ns\rfloor$ collisions about $n(1-s/(\alpha-1))$ blocks remain, so the survival probability of the singleton is approximately $\prod_i\big(1-\frac{X_i+1}{b_{i-1}}\big)\approx(1-s/(\alpha-1))^{\alpha}$ when the mean of $X_i+1$ is $\alpha/(\alpha-1)$; this is the tail $\mathbb P(\sigma>u)=(1-u)^{\alpha}$ of $\mathrm{Beta}(1,\alpha)$ at $u=s/(\alpha-1)$. Feeding $\sigma$ into the deterministic time change of the block-counting process gives $T$. Equivalently, $T^{(n)}$ is the first point of a Cox process whose intensity is a function of the block-counting process of the other $n-1$ individuals, and the small-time law of large numbers for that process yields the density $f_T$.

## Sources

- Jean-Stéphane Dhersin, Fabian Freund, Arno Siri-Jégousse and Linglong Yuan, *On the length of an external branch in the Beta-coalescent*, *Stochastic Processes and their Applications* 123 (2013), 1691–1715, <https://doi.org/10.1016/j.spa.2012.12.010>; preprint arXiv:1201.3983, <https://doi.org/10.48550/arXiv.1201.3983>. Numbering of the arXiv version: Theorem 3.1, Corollary 3.2, Theorem 5.2, Corollary 5.3; second proof in Section 6.
