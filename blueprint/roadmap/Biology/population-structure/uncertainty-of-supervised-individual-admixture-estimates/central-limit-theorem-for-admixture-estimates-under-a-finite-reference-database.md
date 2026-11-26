# Central limit theorem for admixture estimates under a finite reference database

**Model.** An individual's genome descends from $K$ ancestral populations with admixture proportions $q \in \mathbb{S}$ (the simplex). At marker $m = 1, \dots, M$ with alleles $i = 1, \dots, I$, population $k$ has allele frequencies $p_{k\cdot m}$, and each allele copy independently comes from population $k$ with probability $q_k$. For genotype counts $x_{im} \in \{0,1,2\}$ the log-likelihood is

$$
\ell(p, q \mid x) = \sum_{m=1}^{M}\sum_{i=1}^{I} x_{im}\log\Bigl(\sum_{k=1}^{K} q_k\,p_{kim}\Bigr).
$$

In the *supervised* setting $p$ is not known but estimated from a reference database of $2N r_k$ allele copies from population $k$ ($r \in \mathbb{S}^\circ$).

**Results.**
1. *(ML estimator.)* $q \mapsto \ell(p, q \mid x)$ is concave; under a non-degeneracy assumption it is strictly concave with a unique maximizer $\hat q$, the ML estimator, which can be characterized as a stable fixed point of the EM-type map $q \mapsto \operatorname{diag}(q)\,\nabla_q\ell(p, q \mid x)$.
2. *(CLT in the reference size.)* Let the estimated frequencies satisfy $P^N \to p$ and $\sqrt{2N}(P^N_{k\cdot m} - p_{k\cdot m}) \Rightarrow Z_{km} \sim N\bigl(0, r_k^{-1}(\operatorname{diag}(p_{k\cdot m}) - p_{k\cdot m}p_{k\cdot m}^\top)\bigr)$, independent over $(k, m)$, and let $\hat Q^N$ maximize $\ell(P^N, \cdot \mid x)$. Then, with $x$ fixed,

$$
\sqrt{4NM}\,(\hat Q^N - \hat q) \Rightarrow N\bigl(0,\ \Sigma_x\,\Gamma_x\,\Sigma_x\bigr), \qquad N \to \infty,
$$

where $\Sigma_x^{-1}$ is the (normalized) negative Hessian of $\ell(p, \cdot \mid x)$ at $\hat q$, and $\Gamma_x$ is the covariance of the score, obtained by propagating the multinomial sampling covariance of each $P^N_{k\cdot m}$ through the derivative of $\nabla_q\ell$ with respect to $p$.

## Depends on

- [Admixture model and the FRAPPE EM algorithm](../admixture-model-and-the-frappe-em-algorithm/README.md)

## Expansion

Errors in $\hat Q^N$ have two sources: the finite number $M$ of markers in the sample (the usual ML fluctuation) and the finite reference database, which perturbs $p$. The second is a delta-method computation: $\hat q$ solves $\nabla_q \ell(p, q) = 0$ on the simplex, so a perturbation $\delta p$ moves the maximizer by $-(\nabla_q^2\ell)^{-1}\nabla_p\nabla_q\ell\,\delta p$, which produces the sandwich covariance $\Sigma_x\Gamma_x\Sigma_x$. Because reference frequencies enter every marker, reference-panel noise does not average out as fast as sample noise, so for small panels it can dominate the uncertainty of reported ancestry proportions.

## Sources

- P. Pfaffelhuber, A. Rohde, "A central limit theorem concerning uncertainty in estimates of individual admixture", arXiv:2110.08348 (2021), Lemma 2.2, Theorem 1, Theorem 2, <https://doi.org/10.48550/arXiv.2110.08348>.
