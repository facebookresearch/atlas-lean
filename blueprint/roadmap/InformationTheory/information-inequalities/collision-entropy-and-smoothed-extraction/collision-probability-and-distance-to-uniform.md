# Collision probability controls distance to uniform

Let $p$ be a distribution on a nonempty finite set $\alpha$ with collision probability $\mathrm{CP}(p) = \sum_a p(a)^2$, and $U$ the uniform distribution on $\alpha$. Then

$$
4\,\delta(p, U)^2 \le |\alpha|\,\mathrm{CP}(p) - 1, \qquad \delta(p,U) \le \frac12\sqrt{|\alpha|\,\mathrm{CP}(p) - 1}.
$$

Moreover $\mathrm{CP}$ is multiplicative over independent products, and some point has mass at least $\mathrm{CP}(p)$.

## Proof sketch

Cauchy-Schwarz on $|\alpha|$ points gives $(\sum_a|p(a) - 1/|\alpha||)^2 \le |\alpha|\sum_a(p(a) - 1/|\alpha|)^2 = |\alpha|\mathrm{CP}(p) - 1$. With the Rényi entropy $H_2 = \log(1/\mathrm{CP})$ and the min-entropy $H_\infty = \log(1/\max_a p(a))$, multiplicativity is additivity of $H_2$ over independent pairs, and $\max_a p(a) \ge \mathrm{CP}(p)$ is $H_\infty \le H_2$; directly, $\mathrm{CP} = \mathbb{E}_{a\sim p}[p(a)] \le \max_a p(a)$.

The following elementary facts are derived here and are not stated in the cited sources. $\mathrm{CP}(p)^2 \le \sum_a p(a)^3$, since this is $\mathbb{E}_{a\sim p}[p(a)]^2 \le \mathbb{E}_{a\sim p}[p(a)^2]$. $\mathrm{CP}$ is invariant under injective relabeling, since the multiset of masses is unchanged. $\mathrm{CP}(p) \ge p(a)^2$ for every $a$, since the sum contains that term.

## Depends on

- [Guessing probability, min-entropy and collision probability](../../../ComputerScience/cryptography/randomness-extraction/guessing-probability-min-entropy-and-collision.md)
- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- T. Holenstein, "Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness", Theory of Cryptography Conference (TCC), 2006, Section 3.3, proof of Lemma 1, inequality (2).
- S. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1-3), 2012, Section 6.1.2, Definition 6.7 and Lemma 6.8, and Section 6.2.1, proof of Theorem 6.18, steps (2) and (3).
