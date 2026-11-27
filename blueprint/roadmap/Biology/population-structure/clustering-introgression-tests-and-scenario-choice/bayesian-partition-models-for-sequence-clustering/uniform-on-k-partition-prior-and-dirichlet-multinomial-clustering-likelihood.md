# Uniform-on-k partition prior and Dirichlet–multinomial clustering likelihood

**Data and partitions.** Let $n$ aligned sequences be observed at $L$ sites, site $j$ having $r_j$ possible variants. A clustering is a partition $S = \{s_1, \dots, s_k\}$ of the $n$ sequences into $k$ nonempty clusters, with $1 \le k \le K$ for a fixed upper bound $K \le n$. Write $n_{cja}$ for the number of sequences in cluster $s_c$ carrying variant $a$ at site $j$, and $n_{cj} = \sum_a n_{cja}$.

**Prior on partitions (hierBAPS).** The number of clusters is uniform on $\{1, \dots, K\}$ and, given $k$, all partitions into $k$ blocks are equally likely:

$$p(S) = \frac{1}{K}\cdot\frac{1}{\mathcal S(n, k)} \propto \frac{1}{\mathcal S(n, k)}, \qquad k = |S|,$$

where $\mathcal S(n, k)$ is the Stirling number of the second kind (the number of partitions of an $n$-set into $k$ nonempty blocks), $\mathcal S(n,k) = \frac{1}{k!}\sum_{i=0}^{k} (-1)^i \binom{k}{i} (k - i)^n$.

**Likelihood.** Within cluster $c$, the variants at site $j$ are i.i.d. multinomial with frequencies $p_{cj} = (p_{cj1}, \dots, p_{cjr_j})$, independently across sites and clusters, and $p_{cj} \sim \mathrm{Dirichlet}(\alpha_{j1}, \dots, \alpha_{jr_j})$. Integrating out the frequencies gives the marginal likelihood

$$p(x \mid S) = \prod_{c=1}^{k} \prod_{j=1}^{L} \frac{\Gamma\big(\sum_a \alpha_{ja}\big)}{\Gamma\big(\sum_a \alpha_{ja} + n_{cj}\big)} \prod_{a=1}^{r_j} \frac{\Gamma(\alpha_{ja} + n_{cja})}{\Gamma(\alpha_{ja})},$$

and the posterior over partitions is $p(S \mid x) \propto p(x \mid S)\, p(S)$, maximized over $S$ by stochastic search.

**Properties.**

- The prior penalizes additional clusters beyond the uniform-on-$k$ choice: since $\mathcal S(n, k)$ increases with $k$ up to its mode $k^\dagger(n)$ and $\mathcal S(n, k) / \mathcal S(n, k-1)$ is large for small $k$ (e.g. $\mathcal S(n,2) = 2^{n-1} - 1$ versus $\mathcal S(n,1) = 1$), a single partition into more blocks receives a much smaller prior mass than one into fewer blocks, for $k \le k^\dagger(n)$.
- Hierarchical reclustering: when only the sequences of one first-stage cluster are reclustered, many sites that are variable elsewhere in the sample are monomorphic within that cluster, so the second-stage model has far fewer polymorphic sites whose frequencies must be estimated per sub-cluster; this increases power to resolve nested lineages that the first stage merges.

## Proof depends on

- [Dirichlet–multinomial conjugacy](../../../../Probability/distributions/continuous/dirichlet-distribution/dirichlet-law/with-density-prod-pow-dirichlet-measure.md)

## Expansion

The Stirling formula counts surjections from $n$ sequences onto $k$ labelled clusters by inclusion–exclusion and divides by $k!$ for unlabelled blocks. The Dirichlet–multinomial factor is the standard conjugate integral $\int \prod_a p_a^{n_a}\,\mathrm{Dir}(p \mid \alpha)\,dp = \frac{B(\alpha + n)}{B(\alpha)}$ with $B$ the multivariate beta function. Uniform-on-$k$ versus uniform-on-partitions: a uniform prior on all partitions would weight $k$ in proportion to $\mathcal S(n,k)$, strongly favouring many clusters; dividing by $\mathcal S(n,k)$ removes that combinatorial weight. Because both prior and likelihood are available in closed form, the posterior can be optimized directly over partitions rather than by Markov chain Monte Carlo over continuous parameters. The spatially explicit BAPS variant replaces the partition prior by a spatial prior over a tessellation of the sample locations that favours geographically coherent clusters; its parameters, like the allele frequencies, are integrated out analytically, which is what allows posterior-mode search instead of MCMC.

## Sources

- L. Cheng, T. R. Connor, J. Sirén, D. M. Aanensen, J. Corander, "Hierarchical and spatially explicit clustering of DNA sequences with BAPS software", Molecular Biology and Evolution (2013), Materials and Methods ("New Approaches": hierBAPS uniform prior on $k$ with partition probability proportional to $1/\mathcal S(n,k)$; multinomial likelihood with conjugate Dirichlet priors) and Results (hierarchical reclustering), <https://doi.org/10.1093/molbev/mst028> (PMC3670731).
