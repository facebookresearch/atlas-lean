# Site clustering statistic for rate variation

Consider the rates-across-sites $r$-state Poisson model on a phylogeny $T$ with edge weights in $[f,g]$ and tree metric $d$, with i.i.d. site rates $\Lambda_1,\dots,\Lambda_k$ and leaf states $\sigma^i_a$ at site $i$. Let $q_\infty = \sum_x \pi_x^2$ and $p_\infty = 1 - q_\infty$. Call a set $\Upsilon$ of leaf pairs **$\gamma_s$-sparse** if the paths of distinct pairs in $\Upsilon$ are edge-disjoint, $|\Upsilon| \ge \gamma_s n$, and $2f \le d(a,b) \le M$ for every $(a,b) \in \Upsilon$; a greedy procedure produces one with $\gamma_s = 2^{-2\lfloor M/f\rfloor - 2}$. For a site $i$ define

$$\mathcal U_i = \frac{1}{|\Upsilon|}\sum_{(a,b)\in\Upsilon} p_\infty^{-1}\big[\mathbf 1\{\sigma^i_a = \sigma^i_b\} - q_\infty\big], \qquad U_\Upsilon(\lambda) = \frac{1}{|\Upsilon|}\sum_{(a,b)\in\Upsilon} e^{-\lambda d(a,b)},$$

so that $\mathbb E[\mathcal U_i \mid \Lambda_i] = U_\Upsilon(\Lambda_i)$.

**Proposition (independence).** If the paths of distinct pairs in $\Upsilon$ are edge-disjoint, the indicators $\{\mathbf 1\{\sigma_a = \sigma_b\}\}_{(a,b)\in\Upsilon}$ are mutually independent.

**Proposition (concentration).** For a $\gamma_s$-sparse $\Upsilon$ and every $\zeta > 0$ there is $c = c(M,f) > 0$ with

$$\mathbb P\big[\,|\mathcal U_i - U_\Upsilon(\Lambda_i)| \ge \zeta \,\big|\, \Lambda_i\big] \le 2\exp(-c\,\zeta^2 n) \quad \text{a.s.}$$

**Proposition (separation).** If $\lambda - \lambda' \ge \beta \ge 0$, then

$$U_\Upsilon(\lambda') - U_\Upsilon(\lambda) \ge e^{-\lambda M}\big(e^{2f\beta} - 1\big).$$

Together these say that on large trees a single site's pairwise agreement statistic reveals its rate up to $O(n^{-1/2})$ error, so sites can be clustered by rate.

## Expansion

Under the Poisson model $\mathbb P[\sigma_a = \sigma_b] = q_\infty + p_\infty e^{-d(a,b)}$, so after centring and scaling each term has conditional mean $e^{-\Lambda_i d(a,b)}$. Edge-disjoint paths make the indicators functions of disjoint sets of independent edge channels, hence independent; Hoeffding's inequality over $|\Upsilon| \ge \gamma_s n$ terms gives the concentration bound. For separation, each term satisfies $e^{-\lambda' d} - e^{-\lambda d} = e^{-\lambda d}(e^{(\lambda-\lambda')d} - 1) \ge e^{-\lambda M}(e^{2f\beta}-1)$ because $2f \le d \le M$. In practice $\Upsilon$ is unknown and is built from estimated agreement frequencies, which need only $k \ge C\log n$ sites.

## Sources

- Elchanan Mossel, Sebastien Roch, "Identifiability and inference of non-parametric rates-across-sites models on large-scale phylogenies", arXiv (2011). Section 3, Propositions 1–5 and Definition 6; Section 4, Proposition 6. <https://doi.org/10.48550/arXiv.1108.0129>. Published version: Journal of Mathematical Biology 67(4) (2013), 767–797, <https://doi.org/10.1007/s00285-012-0571-4>; locators above refer to the arXiv version.
