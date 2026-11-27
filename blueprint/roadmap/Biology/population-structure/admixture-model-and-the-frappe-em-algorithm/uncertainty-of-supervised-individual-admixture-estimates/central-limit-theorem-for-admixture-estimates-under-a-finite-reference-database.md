# Central limit theorem for admixture estimates under a finite reference database

**Model.** An individual's genome descends from $K$ ancestral populations with admixture proportions $q \in \mathbb{S}$ (the simplex in $\mathbb R^K$, with interior $\mathbb S^\circ$). At marker $m = 1, \dots, M$ with alleles $i = 1, \dots, I$, population $k$ has allele frequencies $p_{k\cdot m}$, and each of the two allele copies independently comes from population $k$ with probability $q_k$. For genotype counts $x_{im} \in \{0,1,2\}$ with $\sum_i x_{im} = 2$, the log-likelihood scaled by $1/(2M)$ is, up to a constant depending only on $x$,

$$
\ell(p, q \mid x) = \frac{1}{2M}\sum_{m=1}^{M}\sum_{i=1}^{I} x_{im}\log\Bigl(\sum_{k=1}^{K} q_k\,p_{kim}\Bigr).
$$

Assume (A1) whenever $x_{im} > 0$ some $p_{kim} > 0$, and (A2, identifiability) for every $s \in \mathbb R^K \setminus \{0\}$ with $\sum_k s_k = 0$ there are $i, m$ with $x_{im} > 0$ and $\sum_k s_k p_{kim} \ne 0$, so that no reference population is a mixture of the others on the observed alleles. In the *supervised* setting $p$ is not known but estimated from a reference database of $2N r_k$ allele copies from population $k$ ($r \in \mathbb{S}^\circ$).

**Results.**

1. *(ML estimator.)* Under (A1), $q \mapsto \ell(p, q \mid x)$ is concave on $\mathbb S$; under (A1) and (A2) it is strictly concave and has a unique maximizer $\hat q$, the ML estimator. A point $q^* \in \mathbb S^\circ$ is the maximizer if and only if $\nabla_q\ell(p, q^* \mid x) = \mathbf 1$: the score vanishes in the tangent directions $s$ with $\sum_k s_k = 0$, while the ambient gradient equals the Lagrange multiplier $1$ in every coordinate.
2. *(Fixed-point characterization.)* With the scaled likelihood, the EM-type map $L(q) = \operatorname{diag}(q)\,\nabla_q\ell(p, q \mid x)$ maps $\mathbb S$ to itself, since its entries sum to $\frac1{2M}\sum_{i,m} x_{im} = 1$. Under (A1) and (A2), for $q^* \in \mathbb S^\circ$ the following are equivalent: $q^*$ is the global maximizer of $\ell(p, \cdot \mid x)$; $q^*$ is a local maximizer; $q^*$ is a locally stable fixed point of $L$; $q^*$ is the unique locally stable fixed point of $L$.
3. *(CLT in the reference size.)* Assume (A1) and (A2), and that the limiting maximizer $\hat q$ lies in the interior $\mathbb S^\circ$. Let the estimated frequencies satisfy $P^N \to p$ in probability and $\sqrt{2N}(P^N_{k\cdot m} - p_{k\cdot m}) \Rightarrow Z_{km} \sim N\bigl(0, r_k^{-1}(\operatorname{diag}(p_{k\cdot m}) - p_{k\cdot m}p_{k\cdot m}^\top)\bigr)$, independent over $(k, m)$, and let $\hat Q^N$ maximize $\ell(P^N, \cdot \mid x)$. Then, with $x$ fixed,

$$
\sqrt{4NM}\,(\hat Q^N - \hat q) \Rightarrow N\bigl(0,\ \Sigma_x\,\Gamma_x\,\Sigma_x\bigr), \qquad N \to \infty,
$$

where $\Sigma_x^{-1} = -\nabla_q^2\ell(p, \hat q \mid x)$ is the negative Hessian of the scaled log-likelihood at $\hat q$, and

$$
\Gamma_x = \frac{1}{2M}\sum_{m=1}^M\sum_{i,j=1}^I \Delta(x_{im}, p_{\cdot im})\,\operatorname{diag}(r^{-1})\,\operatorname{diag}\bigl(p_{\cdot im}(\delta_{ij} - p_{\cdot jm})\bigr)\,\Delta(x_{jm}, p_{\cdot jm})^\top, \qquad \Delta(x, p) = x\Bigl(\frac{E_K}{\langle \hat q, p\rangle} - \frac{p\,\hat q^\top}{\langle \hat q, p\rangle^2}\Bigr),
$$

with $E_K$ the $K \times K$ identity, is the covariance of the score obtained by propagating the multinomial sampling covariance of each $P^N_{k\cdot m}$ through the derivative of $\nabla_q\ell$ with respect to $p$. The limit is degenerate along $\mathbf 1$, since $\hat Q^N$ and $\hat q$ both sum to one.

## Expansion

Errors in $\hat Q^N$ have two sources: the finite number $M$ of markers in the sample (the usual ML fluctuation) and the finite reference database, which perturbs $p$. The second is a delta-method computation: an interior $\hat q$ solves the first-order condition $\nabla_q \ell(p, q) = \mathbf 1$ (a zero tangent score), so a perturbation $\delta p$ moves the maximizer by $-(\nabla_q^2\ell)^{-1}\nabla_p\nabla_q\ell\,\delta p$ to first order, which produces the sandwich covariance $\Sigma_x\Gamma_x\Sigma_x$. Because reference frequencies enter every marker, reference-panel noise does not average out as fast as sample noise, so for small panels it can dominate the uncertainty of reported ancestry proportions.

## Sources

- Peter Pfaffelhuber and Angelika Rohde, "A central limit theorem concerning uncertainty in estimates of individual admixture", *Theoretical Population Biology* 148 (2022), 28–39, <https://doi.org/10.1016/j.tpb.2022.09.003>. Numbering as in the preprint arXiv:2110.08348v2, <https://arxiv.org/abs/2110.08348v2>: Definition 2.1 and equation (1) (scaled log-likelihood), Assumptions 1–2, Lemma 2.5, Theorem 1 and Remark 2.10, Theorem 2.
