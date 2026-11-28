# The GAN value is minimized by distribution matching

On a finite data space let $P,Q$ be probability laws and $M=(P+Q)/2$. Optimize the original discriminator over all maps to $[0,1]$. In natural logarithms the resulting generator value is

$$\max_D V(D,Q)=-\log4+\operatorname{KL}(P\|M)+\operatorname{KL}(Q\|M).$$

Each term with zero numerator contributes zero. Substitution of the optimal discriminator gives the identity, since $p/(p+q)=p/(2m)$ on the support of $P$. The two divergences are nonnegative, with equality simultaneously exactly when $P=Q$. Thus the minimum over all generator **laws** is $-\log4$, attained only at $Q=P$. This says nothing about uniqueness of network parameters or convergence of alternating gradient updates.

## Depends on

- [Generative adversarial network (GAN) objective](generative-adversarial-objective.md)
- [Kullback–Leibler divergence on a finite space](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)

## Proof depends on

- [Optimal discriminator for a fixed generator](optimal-gan-discriminator.md)
- [Equality in Gibbs' inequality](../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/cross-entropy-eq-shannon-entropy-iff.md)

## Sources

- Goodfellow et al., [*Generative Adversarial Nets*](https://papers.nips.cc/paper_files/paper/2014/hash/f033ed80deb0234979a61f95710dbe25-Abstract.html) (NeurIPS 2014), §4.1, theorem 1 (finite-space specialization).
