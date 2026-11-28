# Number of loci needed to detect a short branch from sequence distances

**Setting.** Under the multispecies coalescent, each of $m$ independent genes (loci) has its own gene tree, and along it sequences of length $k$ evolve under the Jukes–Cantor model. For two sampled sequences $\mathbf s_a,\mathbf s_b$ a *distance-based* method uses only the number of differing sites $\theta(\mathbf s_a,\mathbf s_b) = \|\mathbf s_a - \mathbf s_b\|_1$. For a two-leaf species tree with divergence $d_{12} = 2\tau$ and unit population sizes, $\theta$ is binomial with $k$ trials and random success probability $\tfrac34\big(1 - e^{-2(\tau + Z)}\big)$, where $Z$ is the coalescence time of the two gene lineages in the ancestral population.

To detect a branch of length $f$, compare the species tree $S$ with $d_{12} = 2$ and $S^+$ with $d_{12} = 2 - 2f$; let $\mathbb P_0$ and $\mathbb Q$ be the single-gene laws of $\theta$ under $S$ and $S^+$, and $\mathbb P_0^{\otimes m}, \mathbb Q^{\otimes m}$ their $m$-gene products. The minimal sum of type I and type II errors of any test equals $1 - \|\mathbb P_0^{\otimes m} - \mathbb Q^{\otimes m}\|_{\mathrm{TV}}$.

**Theorem.** Let $k = f^{-2+2\kappa}$ and $m = f^{-1-\mu}$ with $0 < \kappa,\mu < 1$, as $f \to 0$.

1. (*Lower bound.*) For every $\delta > 0$ there is $c > 0$ such that $\|\mathbb P_0^{\otimes m} - \mathbb Q^{\otimes m}\|_{\mathrm{TV}} \le \delta$ whenever $m \le c\,\dfrac{1}{f^2\sqrt k}$.
2. (*Matching upper bound.*) For every $\delta > 0$ there is $c' > 0$ such that $\|\mathbb P_0^{\otimes m} - \mathbb Q^{\otimes m}\|_{\mathrm{TV}} \ge 1 - \delta$ whenever $m \ge c'\,\dfrac{1}{f^2\sqrt k}$, and an efficient test distinguishes the two hypotheses in that case.

Hence distance-based species tree estimation needs

$$m = \Theta\Big(\frac{1}{f^2\sqrt k}\Big)$$

genes to resolve a branch of length $f$, interpolating between $m = \Theta(f^{-2})$ for bounded sequence length and $m = \Theta(f^{-1})$ for very long sequences.

## Expansion

Under $S^+$ the gene lineages can coalesce in the extra branch of length $f$, which happens with probability $\sigma_f = O(f)$; otherwise the distance law is that under $S$. So $\mathbb Q = (1-\sigma_f)\mathbb P_0 + \sigma_f\mathbb P_1$ is a sparse mixture, and the problem becomes sparse signal detection. A gene that coalesced early has a distance shifted by order $fk$ relative to the binomial noise of order $\sqrt k$, so each informative gene carries a signal-to-noise ratio of order $f\sqrt k$. Chi-square bounds on the mixture give the lower bound; a test counting genes with unusually small distances attains it.

## Sources

- Elchanan Mossel, Sébastien Roch, "Distance-based species tree estimation: information-theoretic trade-off between number of loci and sequence length under the coalescent", arXiv (2015). Section 1 (setting, mixture representation, Theorems 1–2), Section 2 (distance distribution and mixture lemmas). <https://doi.org/10.48550/arXiv.1504.05289>. Published version: The Annals of Applied Probability 27(5) (2017), 2926–2955, <https://doi.org/10.1214/16-aap1273>; locators above refer to the arXiv version.
