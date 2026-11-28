# Optimal discriminator for a fixed generator

Fix a generator law $Q$ and real data law $P$ on the same measurable space, with densities $q,p$ relative to a common dominating measure $\mu$ (for instance $P+Q$). Among all measurable discriminators with values in $[0,1]$, an optimizer of the minimax GAN discriminator objective is

$$D^*(x)=\frac{p(x)}{p(x)+q(x)}\quad\text{where }p(x)+q(x)>0.$$

Its value elsewhere does not matter. Pointwise, $p\log d+q\log(1-d)$ is maximized at this ratio; if just one density vanishes, the maximizer is an endpoint. Terms weighted by zero contribute zero. The formula is for an unrestricted discriminator, not necessarily for a given neural-network class.

## Depends on

- [Generative adversarial network (GAN) objective](generative-adversarial-objective.md)

## Sources

- Goodfellow et al., [*Generative Adversarial Nets*](https://papers.nips.cc/paper_files/paper/2014/hash/f033ed80deb0234979a61f95710dbe25-Abstract.html) (NeurIPS 2014), §4.1, proposition 1.
