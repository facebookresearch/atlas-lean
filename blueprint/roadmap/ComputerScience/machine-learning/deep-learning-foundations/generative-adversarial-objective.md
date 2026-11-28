# Generative adversarial network (GAN) objective

A generator $G$ maps noise with law $P_Z$ into the data space, so its output law is $Q=G_\#P_Z$. Given the data law $P$, a discriminator $D$ assigns each input a number in $[0,1]$, interpreted as its probability of being real. The original minimax GAN objective is to minimize over $G$ the supremum over $D$ of

$$V(D,G)=\mathbb E_{X\sim P}\log D(X)+\mathbb E_{Z\sim P_Z}\log(1-D(G(Z))).$$

Logs are natural and $\log0=-\infty$. The two real/fake terms have equal weight. The non-saturating generator surrogate is a different training objective; it is not the minimax value above.

## Sources

- Goodfellow et al., [*Generative Adversarial Nets*](https://papers.nips.cc/paper_files/paper/2014/hash/f033ed80deb0234979a61f95710dbe25-Abstract.html) (NeurIPS 2014), §3, equation (1).
