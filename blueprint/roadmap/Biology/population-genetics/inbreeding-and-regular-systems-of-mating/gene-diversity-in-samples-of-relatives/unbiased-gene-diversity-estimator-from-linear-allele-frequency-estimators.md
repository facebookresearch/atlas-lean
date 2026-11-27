# Unbiased gene diversity estimator from linear allele-frequency estimators

**Setting.** A locus has $I$ alleles with population frequencies $p_1, \dots, p_I \in [0,1]$, $\sum_i p_i = 1$, and gene diversity $H = 1 - \sum_{i=1}^I p_i^2$. A sample has $n$ individuals; individual $k$ has ploidy $m_k$ and $X_k(i)$ is the fraction of its $m_k$ allele copies that are of type $i$. For individuals $j, k$ the kinship coefficient $\Phi_{jk}$ is the probability that an allele copy drawn uniformly from $j$ and one drawn uniformly and independently from $k$ (with replacement when $j = k$) are identical by descent (IBD). Alleles that are IBD are of the same type; alleles that are not IBD are independent draws from $(p_i)$. Hence $\mathbb{E}[X_j(i)] = p_i$ and

$$\mathbb{E}[X_j(i)X_k(i)] = \Phi_{jk}\,p_i + (1 - \Phi_{jk})\,p_i^2 .$$

Let $K = (\Phi_{jk})$ be the $n \times n$ kinship matrix. A linear estimator of $p_i$ is $\breve p_i = \sum_{k=1}^n w_k X_k(i)$ with weights summing to one, $\sum_k w_k = 1$ (the source takes $0 \le w_k \le 1$); it is unbiased.

**Proposition 1 (general estimator).** Let $\rho_2 = \sum_{j=1}^n \sum_{k=1}^n w_j w_k \Phi_{jk} = w^{\mathsf T} K w$ and suppose $\rho_2 < 1$. Then

$$\breve H = \frac{1}{1 - \rho_2}\Big(1 - \sum_{i=1}^I \breve p_i^{\,2}\Big)$$

is an unbiased estimator of $H$, for any ploidies, inbreeding and relatedness.

**Corollary 2 (sample proportions).** With $w_k = m_k / \sum_j m_j$, $\breve p_i$ is the sample proportion $\hat p_i$ and $\tilde H = (1 - \sum_i \hat p_i^2)/(1 - \bar\Phi_2)$, $\bar\Phi_2 = \sum_{j,k} \frac{m_j m_k}{(\sum_x m_x)^2}\Phi_{jk}$, is unbiased.

**Corollary 3 (BLUE).** With $w = K^{-1}\mathbf 1 / (\mathbf 1^{\mathsf T} K^{-1} \mathbf 1)$, $\breve p_i$ is the best linear unbiased estimator $\tilde p_i$ of $p_i$ and

$$\tilde H_{\mathrm{BLUE}} = \frac{1}{1 - \kappa_2}\Big(1 - \sum_{i=1}^I \tilde p_i^{\,2}\Big), \qquad \kappa_2 = w^{\mathsf T} K w = \frac{1}{\mathbf 1^{\mathsf T} K^{-1}\mathbf 1},$$

is unbiased.

**Proposition 5 (bias of the uncorrected estimator).** For an integer $M \ge 2$ (in practice the number of sampled allele copies, which need not be the number $n$ of individuals) let $\hat H(\breve p) = \frac{M}{M-1}\big(1 - \sum_i \breve p_i^{\,2}\big)$ (the Nei–Roychoudhury form). Then

$$\operatorname{Bias}\big[\hat H(\breve p)\big] = \frac{1 - M\rho_2}{M-1}\,H .$$

When $H > 0$ the bias vanishes iff $\rho_2 = 1/M$. This holds when $M = \sum_k m_k$ is the number of sampled allele copies, the individuals are unrelated and non-inbred, and $w_k = m_k/M$: then $\Phi_{kk} = 1/m_k$ and $\Phi_{jk} = 0$ for $j \ne k$, so $\rho_2 = \sum_k m_k/M^2 = 1/M$. Relatives and inbreeding raise $\rho_2$ and make $\hat H$ biased downwards in proportion to $H$.

## Expansion

Expanding $\breve p_i^2$ and using the second-moment identity gives $\mathbb{E}[\breve p_i^2] = \rho_2 p_i + (1-\rho_2)p_i^2$, so $\mathbb{E}[1 - \sum_i \breve p_i^2] = (1 - \rho_2)(1 - \sum_i p_i^2) = (1 - \rho_2) H$; dividing by $1 - \rho_2$ gives Proposition 1, and the bias in Proposition 5 is $\frac{M(1-\rho_2)}{M-1}H - H$. The same identity gives $\operatorname{Var}(\breve p_i) = \rho_2\,p_i(1-p_i)$, so among linear unbiased estimators the variance is minimized by minimizing $w^{\mathsf T}Kw$ subject to $\mathbf 1^{\mathsf T}w = 1$, whose Lagrange solution is the BLUE weight vector of Corollary 3; this is why the BLUE-based estimator tends to have the smaller variance. In simulations and on 645 human microsatellite loci (5795 individuals, 267 populations) the BLUE-based estimator has mean squared error at most that of $\tilde H$ and often below that of the biased $\hat H$, with the largest gains for mixed-ploidy relatives such as male–female sibling pairs at X-linked loci.

## Sources

- A. M. Harris and M. DeGiorgio, "An unbiased estimator of gene diversity with improved variance for samples containing related and inbred individuals of any ploidy", G3: Genes, Genomes, Genetics 7(2) (2017) 671–691, Proposition 1, Corollaries 2–3, Proposition 5 and Eqs. (5)–(8), (12)–(13), <https://doi.org/10.1534/g3.116.037168>, PMCID PMC5295611.
