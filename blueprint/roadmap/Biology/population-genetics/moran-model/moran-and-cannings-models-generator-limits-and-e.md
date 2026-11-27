# Moran and Cannings models: generator limits and effective size

This node covers the diffusion scaling of the Moran model and of exchangeable Cannings models, and the effective population size that the scaling defines.

**Cannings models.** In a [Cannings model](../../coalescent-theory/multiple-merger-coalescents/cannings-models/cannings-model.md) with $M$ haploid individuals, let $(\nu_1,\dots,\nu_M)$ be the exchangeable offspring vector, $\sum_j\nu_j=M$, and $\sigma_M^2=\operatorname{Var}\nu_1$. If $i$ individuals carry an allele, its frequency $x=i/M$ moves in one generation to $x'=M^{-1}\sum_{j\le i}\nu_j$, with

$$\mathbb E[x'\mid x]=x,\qquad \operatorname{Var}(x'\mid x)=\frac{\sigma_M^2\,x(1-x)}{M-1}$$

exactly (the covariance $\operatorname{Cov}(\nu_1,\nu_2)=-\sigma_M^2/(M-1)$ follows from $\operatorname{Var}\sum_j\nu_j=0$). With $c_M=\sigma_M^2/(M-1)$, $\inf_M\sigma_M^2>0$ and the sufficient moment condition $\sup_M\mathbb E[\nu_1^4]<\infty$, the one-generation generator sped up by $1/c_M$,

$$c_M^{-1}\bigl(\mathbb E[f(x')\mid x]-f(x)\bigr)\longrightarrow L_0f(x)=\tfrac12x(1-x)f''(x),$$

uniformly in $x\in\{0,1/M,\dots,1\}$ for $f\in C^3[0,1]$, because the third- and higher-order Taylor terms are $o(c_M)$. The variance effective size is $M_e=(M-1)/\sigma_M^2$. For the Wright–Fisher model $\nu$ is multinomial with $\sigma_M^2=1-1/M$, so $M_e=M$ exactly, recovering the [Wright–Fisher generator limit](../diffusion-theory/diffusion-limit-of-the-wright-fisher-model/tendsto-wf-generator.md).

**Moran model.** In the neutral [Moran model](moran-matrix.md) with $N$ haploids, each event chooses a parent and an individual to die uniformly and independently, so the mutant count moves $\pm1$ with probability $x(1-x)$ each. One event has $\operatorname{Var}(x'\mid x)=2x(1-x)/N^2$, so $N^2/2$ events form one unit of diffusion time, and the generator sped up by $N^2/2$ converges to $L_0$. Counting $N$ events as one generation, one diffusion time unit is $N/2$ generations: the Moran model has effective size $M_e=N/2$ gene copies. With mutant fitness $r_N=1+s$, $s=\sigma/N$, the fixation probability from frequency $x$ converges to Kimura's $u(\alpha,x)$ with $\alpha=Ns/2$ ([diffusion limit of the Moran fixation probability](tendsto-moran-fixation-diffusion.md)).

## Depends on

- [Cannings model of a haploid population](../../coalescent-theory/multiple-merger-coalescents/cannings-models/cannings-model.md)
- [Moran process as a stochastic matrix](moran-matrix.md)
- [Wright–Fisher diffusion limit, generator form](../diffusion-theory/diffusion-limit-of-the-wright-fisher-model/tendsto-wf-generator.md)
- [Diffusion limit of the Moran fixation probability](tendsto-moran-fixation-diffusion.md)

## Expansion

An expansion states each part as a page of its own:

- the exact Cannings one-step variance identity;
- the generator limit under $\inf_M\sigma_M^2>0$ and $\sup_M\mathbb E\nu_1^4<\infty$, with the bound on the third and fourth conditional moments of $x'-x$;
- the Moran generator limit with the time unit stated explicitly ($N^2/2$ events, equivalently $N/2$ generations of $N$ events), distinguishing the convention in which parent and dying individual must differ;
- the identity $(M-1)/\sigma^2=M$ for $\sigma^2=1-1/M$, and the effective size of the Moran model as a [variance effective size](../effective-population-size/effective-population-size-definitions.md) in gene copies.

Prerequisites:

- [Closed form of Kimura's fixation probability](kimura-fixation-half.md)
- [Wright–Fisher diffusion limit, generator form](../diffusion-theory/diffusion-limit-of-the-wright-fisher-model/tendsto-wf-generator.md)
- [Moran process as a stochastic matrix](moran-matrix.md)
- [Inbreeding, variance and eigenvalue effective population sizes](../effective-population-size/effective-population-size-definitions.md)

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 10, Section 1 (statement and proof).
- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer (2008), <https://rd.springer.com/book/10.1007/978-0-387-78168-6> (Moran and Cannings scaling; background).
