# Identifiability of Λ-coalescents and demography from the expected SFS

**Setting.** As in [the expected SFS of a Ξ-coalescent](expected-sfs-from-first-coalescence-times-of-xi-coalescents.md): a coalescent with rates $\Xi(d\mathbf{x})/\zeta(t)$, block-counting rate matrix $\mathbf{Q}$ with $\lambda_k = -(\mathbf{Q})_{kk}$, and expected site frequency spectrum $\boldsymbol{\tau}_n$ of a sample of size $n$. A $\Lambda$-coalescent is the case where $\Xi$ charges only single mergers, with $\Lambda$ a finite measure on $[0,1]$.

**Monotonicity lemma.** For every $\Xi$, the total merger rates satisfy $\lambda_{k+1} = \lambda_k + \frac{k}{\binom{k+1}{2}}(\mathbf{Q})_{k+1,k}$, so $(\lambda_k)_{k\ge2}$ is nondecreasing, and it is strictly increasing in $k$ if and only if $\Xi \in \mathcal{X}$, the measures with $(\mathbf{Q})_{k+1,k} > 0$ for every $k \ge 2$ (a single pairwise merger has positive rate for every sample size). For a $\Lambda$-coalescent, $(\mathbf{Q})_{k+1,k} = \binom{k+1}{2}\int_{[0,1]}(1-x)^{k-1}\Lambda(dx)$, so $\Lambda \in \mathcal{X}$ if and only if $\Lambda([0,1)) > 0$, that is, $\Lambda$ is not of the form $c\,\delta_1$ with $c \ge 0$. The source states the lemma as "For all $\Xi \in \mathcal{X}$ and all $\Lambda$ other than $\Lambda(dx) = \delta_1(dx)$ (i.e., the star coalescent), the sequence $(\lambda_k)_{k \ge 2}$ is strictly increasing", and says "$\mathcal{X}$ contains all $\Lambda$ measures except for $\delta_1$". The page differs because these fail for $\Lambda = c\,\delta_1$ with $c \ne 1$ (only full mergers, so $\lambda_k = c$ for every $k$) and for $\Lambda = 0$ (all rates vanish), and the strict increase needs $\Xi \in \mathcal{X}$, which is the hypothesis the source's proof uses.

**Theorem (identifying the merger measure, constant size).**

1. Among point-mass coalescents $\{\delta_z : z \in [0,1]\}$, the expected SFS of a sample of size $n \ge 3$ determines $z$.
2. Among Beta coalescents $\{\mathrm{Beta}(2-\alpha,\alpha) : \alpha \in [1,2)\}$, the expected SFS with $n \ge 3$ determines $\alpha$.
3. Within the union of Kingman's coalescent under exponential growth $\{\delta_0/(ae^{-bt}) : a,b > 0\}$, the point-mass coalescents and the Beta coalescents above, the expected SFS with $n \ge 4$ determines the model and its parameters. In particular exponential population growth and multiple mergers, which both produce an excess of rare variants, are distinguishable from the expected SFS of four or more sequences.

**Theorem (identifying the size history).** Fix $\Xi \in \mathcal{X}$ (for $\Lambda$-coalescents: every $\Lambda$ with $\Lambda([0,1)) > 0$, see the lemma). Restrict $\zeta$ to the class $\mathcal{M}_K(\mathcal{F})$ of piecewise functions with at most $K$ pieces from a family $\mathcal{F}$ of finite sign-change complexity $\mathcal{S}(\mathcal{F})$ (the supremum of the number of zero crossings of $f_1 - f_2$, $f_1,f_2 \in \mathcal{F}$). Let $\psi^\Xi_n$ be the number of zero entries in the first column of $\mathbf{U}^{-1}$ in the spectral decomposition of $\mathbf{Q}$. If $n \ge 2K + (2K-1)\mathcal{S}(\mathcal{F}) + \psi^\Xi_n$, then each expected SFS is consistent with a unique $\zeta \in \mathcal{M}_K(\mathcal{F})$. Without such a restriction $\zeta$ is not identifiable, already for Kingman's coalescent.

## Depends on

- [Expected SFS of a Ξ-coalescent from first-coalescence times](expected-sfs-from-first-coalescence-times-of-xi-coalescents.md)
- [The Beta-coalescent measure on the unit interval](../../merger-rates-and-beta-coalescents/beta-lambda.md)

## Expansion

Since $\boldsymbol{\tau}_n$ is in bijection with the expected TMRCAs, identifiability reduces to whether the TMRCA vector separates parameters. For the one-parameter families with constant size, the expected TMRCAs of samples of sizes $2$ and $3$ already separate the parameter values, while the additional growth parameter of the exponential Kingman model needs a fourth sample size. For the size history, the first-coalescence times $c_{k,k}$ are Laplace-type transforms of $\zeta$ at the distinct rates $\lambda_k$, and a Descartes rule-of-signs argument bounds the number of sign changes of the difference of two candidate histories, which forces them to coincide when $n$ is large enough.

## Sources

- Jeffrey P. Spence, John A. Kamm and Yun S. Song, "The Site Frequency Spectrum for General Coalescents", *Genetics* 202(4) (2016), 1549–1561. <https://doi.org/10.1534/genetics.115.184101>
- Preprint version (the locators in this item follow its numbering): Jeffrey P. Spence, John A. Kamm and Yun S. Song, "The site frequency spectrum for general coalescents", Genetics 202 (2016); arXiv:1510.05631, Section 4 (identifiability theorems for point-mass, Beta and growth-versus-multiple-merger models, monotonicity lemma, and the size-history theorem), <https://doi.org/10.48550/arXiv.1510.05631>.
