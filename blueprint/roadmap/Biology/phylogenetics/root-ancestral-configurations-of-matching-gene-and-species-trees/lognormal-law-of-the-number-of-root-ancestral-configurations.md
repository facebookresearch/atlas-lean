# Lognormal law of the number of root ancestral configurations

**Setting.** For a gene tree and a species tree, an *ancestral configuration* at an internal node of the species tree is a distinct set of gene lineages that can be present at that node; the *root configurations* $c_r$ are those at the root. Their number measures the cost of computing gene tree probabilities under the multispecies coalescent. Assume the gene tree and species tree have the same labeled topology with $n$ leaves, drawn at random.

**Recursive structure.** Let $R_n$ be the number of root configurations; $R_1 = 0$ and for $n \ge 2$

$$R_n \stackrel{d}{=} (R_{I_n} + 1)(R^*_{n-I_n} + 1),$$

with $R^*$ an independent copy and $I_n$ the size of the left root subtree: under the uniform distribution on labeled topologies (equivalently ordered unlabeled topologies), $\mathbb{P}[I_n = j] = C_{j-1}C_{n-j-1}/C_{n-1}$ with Catalan numbers $C_k$; under the Yule-Harding distribution (equivalently ordered histories), $I_n$ is uniform on $\{1,\dots,n-1\}$.

**Theorem.**
1. (Uniform model) $\big(\log c_r - \mathbb{E}_n[\log c_r]\big)/\sqrt{\mathbb{V}_n[\log c_r]} \to \mathcal{N}(0,1)$ with $\mathbb{E}_n[\log c_r] \sim \mu n$, $\mathbb{V}_n[\log c_r] \sim \sigma^2 n$, $(\mu,\sigma^2) \approx (0.272, 0.034)$.
2. (Yule-Harding model) The same lognormal limit holds with $(\mu,\sigma^2) \approx (0.351, 0.008)$.
3. (Yule-Harding moments) $\mathbb{E}_n[c_r] \sim k_e^n$ with $k_e = 1/(1 - e^{-2\pi\sqrt{3}/9}) \approx 1.42538682$, and $\mathbb{V}_n[c_r] \sim k_v^n$ with $k_v \approx 2.0449954971$; the total number of configurations over all nodes has the same exponential growth rates.

## Expansion

The root of the species tree sees, from each root subtree, either the single lineage that has coalesced at that subtree's root or one of its own root configurations, hence the product of $(R+1)$ factors. Taking logarithms turns the multiplicative recursion into an additive one, $\log(R_n) \approx \log(R_{I_n}+1) + \log(R^*_{n-I_n}+1)$, to which central limit theorems for additive functionals of random split trees apply, giving linear mean and variance. Under the uniform model $e^{0.272n} \approx 1.313^n$ is close to but below the mean growth $(4/3)^n$, as expected from Jensen's inequality for a lognormal. Yule-Harding trees are more balanced, giving faster typical growth $e^{0.351n}$ and smaller fluctuations; the mean growth $k_e$ comes from singularity analysis of the generating function.

## Sources

- Filippo Disanto, Michael Fuchs, Ariel R. Paningbatan and Noah A. Rosenberg, "The distributions under two species-tree models of the number of root ancestral configurations for matching gene trees and species trees", arXiv:2006.09106 (2020), Propositions 1-7, <https://doi.org/10.48550/arXiv.2006.09106>.
