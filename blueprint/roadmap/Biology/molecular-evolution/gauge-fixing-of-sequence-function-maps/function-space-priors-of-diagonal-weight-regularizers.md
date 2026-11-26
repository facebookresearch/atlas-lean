# Function-space priors of diagonal weight regularizers

Use the subsequence weight space of sequences of length $\ell$ over an alphabet of size $\alpha$: weights $w_{(S,s)}$ for position sets $S \subseteq [\ell]$ and characters $s \in \mathcal A^S$, with landscape $f(x) = \sum_{S} w_{(S, x[S])}$. A positive diagonal regularizer $\Lambda$ corresponds to independent priors $w_{(S,s)} \sim \mathcal N(0, \Lambda_{(S,s),(S,s)}^{-1})$, and it induces the Gaussian process prior on $f$ with kernel $K = \Phi \Lambda^{-1} \Phi^{\mathsf T}$, i.e.

$$K(x,y) = \sum_{S \subseteq \{p\,:\,x_p = y_p\}} \Lambda_{(S, x[S]),(S, x[S])}^{-1}.$$

Let $d(x,y)$ be the Hamming distance and $\mathcal K_k(d) = \sum_{i=0}^{k} (-1)^i (\alpha - 1)^{k-i}\binom{d}{i}\binom{\ell - d}{k - i}$ the Krawtchouk polynomials.

1. **Product-weighted regularizer.** For finite $\lambda > 0$ and a product distribution $\pi(x) = \prod_p \pi^p_{x_p}$ with full support, the regularizer $\Lambda_{(S,s),(S,s)} = \lambda^{|S|}\prod_{p \in S}\pi^p_{s_p}$ induces

$$K(x,y) = \prod_{p\,:\,x_p = y_p}\Bigl(1 + \frac{1}{\pi^p_{x_p}\lambda}\Bigr).$$

For uniform $\pi$ this is the geometric decay kernel $K(x,y) = (1 + \alpha/\lambda)^{\ell - d(x,y)}$, whose correlations decay faster with Hamming distance when $\lambda$ is small.
2. **Order-dependent regularizer.** If $\Lambda_{(S,s),(S,s)} = a_{|S|}$ with $a_j > 0$, then $\Lambda$ induces the variance-component kernel

$$K(x,y) = \sum_{k=0}^{\ell}\Bigl(\sum_{j=k}^{\ell}\frac{1}{\alpha^{j} a_j}\binom{\ell - k}{j - k}\Bigr)\mathcal K_k\bigl(d(x,y)\bigr).$$

Not every variance-component kernel arises this way; one does iff a certain triangular linear system for the $1/a_j$ has an entrywise positive solution.

## Depends on

- [Gauge regularizers inducing Gaussian process priors](gauge-regularizers-inducing-gaussian-process-priors.md)

## Expansion

Penalized regression with $\Lambda$ equals MAP estimation with the weight prior $\mathcal N(0, \Lambda^{-1})$, whose image under $\Phi$ is $\mathcal N(0, \Phi\Lambda^{-1}\Phi^{\mathsf T})$; so for diagonal $\Lambda$ the kernel is a sum over subsequences shared by $x$ and $y$, i.e. over subsets of the positions where they agree. In item 1 the summand factorizes over positions, and summing over subsets of the agreeing positions gives the product $\prod (1 + 1/(\pi^p_{x_p}\lambda))$; non-uniform $\pi$ makes the prior heteroskedastic, with smaller variance for sequences likely under $\pi$. In item 2 the summand depends only on $|S|$, so $K(x,y) = \sum_j \binom{\ell - d(x,y)}{j}/a_j$, which is expanded in the Krawtchouk basis using a binomial identity, producing variance components $\lambda_k$ indexed by interaction order. The upshot is that the common practice of shrinking higher-order interaction weights more strongly corresponds to a prior under which nearby sequences have strongly correlated phenotypes.

## Sources

- S. Petti, C. Martí-Gómez, J. B. Kinney, J. Zhou, D. M. McCandlish, "On learning functions over biological sequence space: relating Gaussian process priors, regularization, and gauge fixing", *Journal of Mathematical Biology* (2026), Sections 4–5 (Definitions 8–10, Theorems 5–6, Corollary 1, Lemma 9), <https://doi.org/10.1007/s00285-026-02398-y> (PMC13128692).
