# Two-state ancestry covariance

Let $\alpha, r \in \mathbb{R}$, $n \in \mathbb{N}$, $\pi = (\alpha, 1 - \alpha)$ on the states
$\{0, 1\}$, $c = (1 - r)^n$, and $I = (1, 0)$ the indicator of state $0$. Then, with
$K = K_\pi(c)$ the [sticky kernel](sticky-kernel.md),

$$\sum_{i, j} \pi(i) K(i, j)\, I(i) I(j) - \Bigl(\sum_i \pi(i) I(i)\Bigr)^2 = \alpha (1 - \alpha)(1 - r)^n .$$

In the local-ancestry chain of a two-way pulse admixture, with ancestry proportions $\alpha$ and
$1 - \alpha$, recombination fraction $r$ per meiosis and $n$ meioses since admixture (so that $c$ is
the probability of no recombination between the two sites), the left side is the covariance of the
indicators of ancestry $0$ at the two sites. The kernel form of the ancestry pair is a modelling
assumption, not derived from a genealogy.

## Sources

- R. Chakraborty and K. M. Weiss, *Admixture as a tool for finding linked genes and detecting that
  difference from allelic association between loci*, Proceedings of the National Academy of
  Sciences of the USA 85 (1988), 9119–9123.
