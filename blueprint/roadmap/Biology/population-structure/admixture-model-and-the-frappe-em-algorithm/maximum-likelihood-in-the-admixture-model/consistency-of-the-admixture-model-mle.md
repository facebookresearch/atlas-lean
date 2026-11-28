# Consistency of the admixture model MLE

**Model.** There are $N$ individuals, $M$ bi-allelic markers and $K$ ancestral populations. Individual $i$ has ancestry vector $q_{i,\cdot}\in\mathbb S^K$ (the probability simplex) and population $k$ has allele frequency $p_{k,m}\in[0,1]$ at marker $m$. The genotypes $X_{i,m}\in\{0,1,2\}$ are independent with

$$
X_{i,m}\sim\mathrm{Bin}(2,c_{i,m}),\qquad c_{i,m}=\langle q_{i,\cdot},p_{\cdot,m}\rangle=\sum_{k=1}^Kq_{i,k}p_{k,m}.
$$

The maximum likelihood estimator $(\hat Q^N,\hat P^M)$ maximizes $\sum_{i,m}\log\mathbb{P}_{q,p}(X_{i,m}=x_{i,m})$ over the parameter space $\Theta$.

**Non-identifiability.** For any invertible $K\times K$ matrix $S_K$, $\langle q_{i,\cdot},p_{\cdot,m}\rangle=\langle q_{i,\cdot}S_K,S_K^{-1}p_{\cdot,m}\rangle$, so the likelihood is unchanged whenever $q S_K$ is again a set of ancestries and $S_K^{-1}p$ a set of frequencies; permutation matrices (label switching) are the simplest case. Hence the MLE need not be unique.

**Theorem (consistency for non-unique MLEs).** Let $(q^0,p^0)$ be the true parameters, $c^0_{i,m}$ the true success probabilities, and

$$
d\bigl((q,p),(q^0,p^0)\bigr)=\sum_{i=1}^N\frac{|q_{i,\cdot}-q^0_{i,\cdot}|}{2^i}+\sum_{m=1}^M\frac{|p_{\cdot,m}-p^0_{\cdot,m}|}{2^m},\qquad
\mathcal M(\gamma)=\Bigl\{(q,p)\in\Theta:\lim_{M,N\to\infty}\frac{1}{MN}\sum_{m,i}|c_{i,m}-c^0_{i,m}|<\gamma\Bigr\},
$$

the set of parameters whose success probabilities are, on average, within $\gamma$ of the true ones. Then for all $\epsilon,\gamma>0$,

$$
\lim_{M,N\to\infty}\mathbb{P}\Bigl(\min\bigl\{d\bigl((\hat Q^N,\hat P^M),(q,p)\bigr):(q,p)\in\mathcal M(\gamma)\bigr\}\ge\epsilon\Bigr)=0 .
$$

**Uniqueness criteria.** For $K=2$, the only admissible reparametrizations $S_2$ are permutations if and only if there are markers $m_1,m_2$ with $\hat p_{1,m_1}=1$, $\hat p_{1,m_2}=0$ and $\hat p_{2,m_j}\ne\hat p_{1,m_j}$, and individuals $i_1,i_2$ with $\hat q_{i_1,1}=1$, $\hat q_{i_2,1}=0$. For general $K$, if every population has an individual with $\hat q_{i,\cdot}=e_k$ and, for all $j\ne k$, a marker with $\hat p_{\cdot,m}=e_k+a_{j,m}e_j$, $0<a_{j,m}<1$, with all the $a_{j,m}$ distinct, then only permutations remain. With allele frequencies known and a single individual, the ancestry MLE is consistent provided the averaged Kullback–Leibler divergence between $\mathrm{Bin}(2,c_{i,m})$ and $\mathrm{Bin}(2,c^0_{i,m})$ stays bounded away from zero for $q\ne q^0$.

## Depends on

- [Parameters of the admixture model](../params.md)
- [Admixture log-likelihood](../admixture-log-lik.md)

## Expansion

The proof follows the Hoadley-type argument for independent but not identically distributed observations: the normalized log-likelihood ratio is uniformly negative outside any $d$-neighbourhood of the set of parameters whose success probabilities $c_{i,m}$ agree with the true ones on average, and the parameter space is compact under the weighted metric $d$. Because the likelihood only sees the products $c_{i,m}$, consistency can only hold modulo the set $\mathcal M$ of near-equivalent parametrizations; the uniqueness criteria describe when the reparametrizations allowed by the simplex constraints collapse to label switching, as in the presence of "pure" individuals and anchoring markers.

## Sources

- Carola Sophia Heinzel, "Consistency and central limit results for the maximum likelihood estimator in the Admixture Model", *Theor. Popul. Biol.* 166 (2025), 70-79. <https://doi.org/10.1016/j.tpb.2025.10.001>
- Preprint version (the locators in this item follow its numbering): Carola Sophia Heinzel, *Consistency and central limit results for the maximum likelihood estimator in the admixture model*, arXiv (2025). Definition 2.1 (admixture model), Definition 2.3 (label switching), Theorem 1 (consistency), Corollaries 5.2, 5.3 (uniqueness), Corollary 5.10 (known allele frequencies). <https://doi.org/10.48550/arXiv.2507.19564>. The preprint defines $\mathcal M(\gamma)$ with "$\ge\gamma$", a misprint: its proof needs the limiting expected log-likelihood ratio to be strictly negative on $\{\min d(\cdot,\mathcal M)\ge\epsilon\}$, which holds only when $\mathcal M$ is the set of near-equivalent parameters, and its lead-in to Theorem 1 says the MLE tends towards a value with almost the same likelihood as the true parameters.
