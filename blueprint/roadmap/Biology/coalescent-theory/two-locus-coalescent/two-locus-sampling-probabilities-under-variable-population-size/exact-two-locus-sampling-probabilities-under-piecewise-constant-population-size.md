# Exact two-locus sampling probabilities under piecewise-constant population size

**Setting.** Two bi-allelic loci are sampled from $n$ haplotypes. A sample configuration $\mathbf{n} = (n_{ij}, n_{i\ast}, n_{\ast j})$ counts fully specified haplotypes ($c$-types, alleles $i$ and $j$ at the two loci) and haplotypes typed at only one locus ($a$- and $b$-types). Under the coalescent with recombination (scaled recombination rate $\rho$, mutation rate $\theta$ with transition matrix $P$), effective population size is piecewise constant: on the interval $(t_d, t_{d+1}]$, with $-\infty = t_{-D} < t_{-D+1} < \dots < t_0 = 0$ (the last interval extending to the infinite past), every pair of lineages coalesces at rate $1/\eta_d$. Let $\mathbb{P}_0(\mathbf{n})$ be the probability that the sample has configuration $\mathbf{n}$.

**Theorem (exact formula).** Consider the forward-in-time **augmented Moran model** $\tilde M_t$ with state space $\mathcal{N} = \{\mathbf{n} : n^{(abc)} = (k,k,n-k),\ 0 \le k \le n\}$, in which alleles are copied between lineages (at rate $1/\eta_d$ per pair) and mutate (at rate $\theta/2$), each $c$-type splits into an $a$- and a $b$-type at rate $\rho/2$, and each pair of $a$- and $b$-types "recoalesces" into a $c$-type at rate $1/\eta_d$; let $\tilde\Lambda^d$ be its rate matrix on $(t_d, t_{d+1}]$ and $\tilde\lambda^{d}$ its stationary distribution. Let $\gamma^d = (\gamma^d_0,\dots,\gamma^d_n)$ be the stationary law of the process counting $c$-types under recombination and recoalescence alone, lifted to $\tilde\gamma^d_{\mathbf{n}} = \gamma^d_m$ when $\mathbf{n}$ has $m$ $c$-types. Define, with componentwise product $\odot$ and quotient $\div$,

$$\mathbf{p}^{-D+1} = \tilde\lambda^{-D} \div \tilde\gamma^{-D}, \qquad \mathbf{p}^{d+1} = \Big[\big(\mathbf{p}^{d} \odot \tilde\gamma^{d}\big)\,e^{\tilde\Lambda^{d}(t_{d+1} - t_d)}\Big] \div \tilde\gamma^{d}.$$

Then $\mathbb{P}_0(\mathbf{n}) = p^0_{\mathbf{n}}$ for every $\mathbf{n} \in \mathcal{N}$; the probabilities of samples with missing alleles follow by marginalisation.

**Complexity.** $\tilde\Lambda^d$ has $O(n^6)$ states but only $O(n^6)$ nonzero entries, so each epoch costs $O(n^6\mathcal{T})$ by sparse matrix-exponential–vector products, where $\mathcal{T}$ is the finite number of sparse matrix–vector products needed for numerical precision; a related approximate formula based on the ordinary Moran model needs only $O(n^3)$ states.

**Theorem (posterior genealogy).** Conditioned on the sample, the ancestral configurations $\{\mathbf{n}_t\}_{t \le 0}$ form a backward-in-time Markov chain with inhomogeneous rates $q^{(t)}_{\mathbf{n},\mathbf{m}}\,\mathbb{P}_t(\mathbf{m})/\mathbb{P}_t(\mathbf{n})$ for $\mathbf{m} \ne \mathbf{n}$, where $q^{(t)}$ are the coalescent-with-recombination rates; this gives an optimal importance-sampling proposal.

## Depends on

- [Two-locus ancestral process for n sequences](../two-locus-ancestral-process-for-n-sequences.md)
- [Coalescent with recombination: ancestral-material state space and generator](../coalescent-with-recombination-ancestral-material.md)

## Expansion

The augmented Moran model is a forward-in-time particle construction: its copying events correspond to coalescences of the backward genealogy, and recombination–recoalescence events track how a $c$-lineage splits into separate ancestors at the two loci and is rejoined. Within one epoch the forward process is time-homogeneous, so its distribution is propagated by one matrix exponential; dividing by the stationary weights $\tilde\gamma^d$ converts between the forward Moran law and the sampling probability, because the number of $c$-types is itself a stationary process independent of allelic types. In the infinitely old first epoch the process is at stationarity, which gives the initial vector. These exact two-locus likelihoods, tabulated over $\rho$, replace the constant-size lookup tables of composite-likelihood estimators of fine-scale recombination such as LDhat, and removing the constant-size assumption reduces spurious recombination hotspots in populations that have grown or passed through bottlenecks.

## Sources

- John A. Kamm, Jeffrey P. Spence, Jeffrey Chan and Yun S. Song, *Two-locus likelihoods under variable population size and fine-scale recombination rate estimation*, Genetics 203(3) (2016), 1381–1399. <https://doi.org/10.1534/genetics.115.184820> Section 2 (background, Moran model), Section 3 (Theorems 1 and 2, augmented Moran rates), Appendix (computational complexity, proofs). Locators use the numbering of the preprint arXiv:1510.06017.
