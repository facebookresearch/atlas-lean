# Chao–Lee species-richness estimator from reconciling add-λ and Turing–Good estimates of unseen mass

**Setting.** A population contains an unknown number $T$ of species with proportions $p_1,\dots,p_T$. A sample of size $n$ observes $N$ distinct species, species $i$ being seen $m_i$ times ($m_i = 0$ for $i > N$), and $n_j$ species are seen exactly $j$ times, so $\sum_j n_j = N$ and $\sum_j j n_j = n$. The unobserved probability is $U = \sum_{i : m_i = 0} p_i$.

Two estimators of $U$ are:

- the unsmoothed **Turing–Good** estimator $\widehat U_{TG} = n_1/n$;
- the **extended add-$\lambda$** estimator for a known $T$: add $\lambda > 0$ to the count of every one of the $T$ species, so $\widehat p_k(\lambda) = (m_k+\lambda)/(T\lambda+n)$ and

$$\widehat U_\lambda = \frac{(T-N)\lambda}{T\lambda+n}.$$

**Lemma (reconciliation).** The equation $\widehat U_\lambda = \widehat U_{TG}$ has the unique solution

$$\widehat T_\lambda = \frac{N + n\widehat U_{TG}/\lambda}{1-\widehat U_{TG}} = n\,\frac{N + n_1/\lambda}{n-n_1},$$

which is exactly the Chao–Lee estimator

$$\widehat T_{CL}(\gamma) = \frac{N}{1-\widehat U_{TG}} + \frac{n\widehat U_{TG}}{1-\widehat U_{TG}}\,\gamma^2$$

with $\gamma^2 = 1/\lambda$. Here $\gamma^2 = T\sum_k p_k^2 - 1$ is the squared coefficient of variation of the species proportions, so the uniform case $\gamma^2 = 0$ recovers the Horvitz–Thompson form $N/(1-\widehat U_{TG})$.

**Bayesian reading.** Under a symmetric Dirichlet prior with density proportional to $\prod_{i=1}^T p_i^{\lambda-1}$ on the simplex, $\lambda \ge 1$, the posterior given the counts is Dirichlet with parameters $m_i + \lambda$, and for $i \ne j$

$$\mathbb{E}(p_i) = \frac{m_i+\lambda}{T\lambda+n},\qquad \mathbb{E}(p_i p_j) = \frac{(m_i+\lambda)(m_j+\lambda)}{(T\lambda+n+1)(T\lambda+n)},\qquad \mathbb{E}(p_k^2) = \frac{(m_k+\lambda+1)(m_k+\lambda)}{(T\lambda+n+1)(T\lambda+n)}.$$

Summing, with $q = \sum_k m_k^2$,

$$\sum_{k=1}^T \mathbb{E}(p_k^2) = \frac{q + n(2\lambda+1) + T(\lambda^2+\lambda)}{(T\lambda+n+1)(T\lambda+n)}.$$

So the add-$\lambda$ estimate is the posterior mean, and $1/\lambda$ plays three roles at once: the Chao–Lee heterogeneity term, the Laplace pseudocount, and the Dirichlet concentration.

## Expansion

Solving $(T-N)\lambda/(T\lambda+n) = n_1/n$ is linear in $T$: $T\lambda(n - n_1) = nN\lambda + n n_1$. The posterior moments are Dirichlet integrals evaluated with the Beta function. Matching the second posterior moment $\sum_k\mathbb{E}(p_k^2)$ to the Good–Toulmin estimate $\widehat V = \sum_j j(j-1)n_j/(n(n-1))$ of $\sum_k p_k^2$, with $T = \widehat T_\lambda$, gives an equation for $\lambda$. This yields simultaneous estimates of $T$, $\gamma^2$ and the prior parameter; the paper notes that the method cannot handle populations with $\gamma^2 > 1$.

## Sources

- L. Cecconi, A. Gandolfi and C. C. A. Sastri, "A New Estimator for the Number of Species in a Population", arXiv:0804.1030 (2008), Sections 2–4 (reconciliation lemma in Section 3; Dirichlet posterior moments in Appendix 1), <https://doi.org/10.48550/arXiv.0804.1030>.
