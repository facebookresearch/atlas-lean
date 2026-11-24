# Likelihood of independent sites is the product of site likelihoods

Let $I$ be a finite set of sites with leaf weights $\mathrm{obs}_k$ for each site $k$, $t$ a [tree](tree.md), $S$ a finite state set and $\pi$ a root distribution with values in a commutative semiring. Then

$$\sum_{\sigma} \prod_{k \in I} \pi(s_k)\, W_k(t, s_k, z_k) = \prod_{k \in I} \mathcal{L}_k,$$

where $\sigma$ ranges over the choices of a root state $s_k$ and a [labeling](labeling.md) $z_k$ for every site $k$, $W_k$ is the [weight](weight.md) with leaf weights $\mathrm{obs}_k$, and $\mathcal{L}_k$ the [site likelihood](likelihood.md) of site $k$.
