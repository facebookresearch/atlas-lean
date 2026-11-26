# Collision probability controls distance to uniform

Let $p$ be a distribution on a nonempty finite set $\alpha$ with collision probability $\mathrm{CP}(p) = \sum_a p(a)^2$, and $U$ the uniform distribution on $\alpha$. Then

$$
4\,\delta(p, U)^2 \le |\alpha|\,\mathrm{CP}(p) - 1, \qquad \delta(p,U) \le \frac12\sqrt{|\alpha|\,\mathrm{CP}(p) - 1}.
$$

Moreover $\mathrm{CP}(p)^2 \le \sum_a p(a)^3$, $\mathrm{CP}$ is multiplicative over independent products, invariant under injective relabeling, at least $p(a)^2$ for every $a$, and some point has mass at least $\mathrm{CP}(p)$.

## Proof sketch

Cauchy-Schwarz on $|\alpha|$ points gives $(\sum_a|p(a) - 1/|\alpha||)^2 \le |\alpha|\sum_a(p(a) - 1/|\alpha|)^2 = |\alpha|\mathrm{CP}(p) - 1$. The inequality $\mathrm{CP}^2 \le \sum p^3$ is $\mathbb{E}_{a\sim p}[p(a)]^2 \le \mathbb{E}_{a\sim p}[p(a)^2]$, and $\mathrm{CP} = \mathbb{E}_{a\sim p}[p(a)] \le \max_a p(a)$.

## Depends on

- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)
- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography Conference (TCC), 2006.
- S. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1-3), 2012.
