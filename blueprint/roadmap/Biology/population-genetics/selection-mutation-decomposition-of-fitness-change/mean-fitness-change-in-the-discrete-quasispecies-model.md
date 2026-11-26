# Mean fitness change in the discrete quasispecies model

**Setting.** A haploid population of types $j$ with frequencies $x_j$ and constant fitnesses $w_j>0$ evolves by the discrete quasispecies (selection–mutation) recursion

$$x_k(t+1) = \frac{1}{\bar w}\sum_j x_j(t)\,w_j\,Q_{jk}, \qquad \bar w = \sum_j x_jw_j,$$

where $Q_{jk} = (1-\mu_j)\delta_{jk} + \mu_jq_{jk}$, $\mu_j$ is the total mutation probability away from $j$ and $q_{jk}$ ($q_{jj}=0$, $\sum_kq_{jk}=1$) is the conditional probability of mutating to $k$. The average effect of the mutation $j\to k$ is $\mathrm{AME}(j\to k) = w_k-w_j$, and the *total mutation effect* of type $j$ is

$$\tau_j = \mu_j\sum_{k\ne j}q_{jk}\,(w_k-w_j),$$

so that the expected fitness of offspring of $j$ is $w_j^{*} = \sum_kw_kQ_{jk} = w_j+\tau_j$.

**Theorem.** The change in mean fitness over one generation is

$$\Delta\bar w = \frac{\mathrm{Var}(w)}{\bar w} + \frac{1}{\bar w}\,\mathbb{E}[w\,\tau],$$

with variance and expectation taken over the current type distribution $x$. If $\mu_j=\mu$ for all $j$, then with $\gamma_j = \sum_{k\ne j}q_{jk}(w_k-w_j)$,

$$\Delta\bar w = \frac{\mathrm{Var}(w)}{\bar w} + \mu\,\mathbb{E}[\gamma] + \frac{\mu}{\bar w}\,\mathrm{Cov}(w,\gamma).$$

The first term is Fisher's selection term; the others are the fitness effect of mutation, weighted by parental fitness.

## Expansion

The new mean fitness is $\bar w(t+1) = \sum_kx_k(t+1)w_k = \frac{1}{\bar w}\sum_jx_jw_jw_j^{*} = \frac{1}{\bar w}\big(\mathbb{E}[w^2]+\mathbb{E}[w\tau]\big)$, and subtracting $\bar w = \mathbb{E}[w]$ gives the decomposition since $\mathbb{E}[w^2]/\bar w-\bar w = \mathrm{Var}(w)/\bar w$. With uniform $\mu$, $\tau=\mu\gamma$ and $\mathbb{E}[w\gamma] = \bar w\,\mathbb{E}[\gamma]+\mathrm{Cov}(w,\gamma)$. This is a Price-equation form in which the transmission term is the average causal effect of mutation on offspring fitness.

## Sources

- J. Iacovacci, "Evolution as a process of causal inference", arXiv:2606.03384, Section 3, Definition of the total mutation effect, Theorem 3.2 and Corollary 3.3. <https://doi.org/10.48550/arXiv.2606.03384>
