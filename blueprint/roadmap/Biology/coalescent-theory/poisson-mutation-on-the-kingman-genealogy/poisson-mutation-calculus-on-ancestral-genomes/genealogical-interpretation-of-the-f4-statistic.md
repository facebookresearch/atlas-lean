# Genealogical interpretation of the $f_4$ statistic

**Setting.** Fix the (unknown) pedigree and ancestral recombination graph of a population and treat it as a fixed object; the only randomness is the mutation process, a Poisson process on pairs (ancestral chromosome $a$, site $\ell$) with intensity $\mu(\ell)$ per generation, under the infinite-sites model. For sets $X,Y,U,V$ of $n_X,n_Y,n_U,n_V$ sampled chromosomes genotyped at $G$ sites, with alternate-allele frequencies $p_X(\ell)$ and so on, the [$f_4$ statistic](../../../population-structure/patterson-s-f-statistics/f4.md) is

$$f_4(X,Y;U,V)=\frac{1}{G}\sum_{\ell=1}^{G}\bigl(p_X(\ell)-p_Y(\ell)\bigr)\bigl(p_U(\ell)-p_V(\ell)\bigr).$$

**Theorem 1.** (I) Let $F_X(a,\ell)$ be the proportion of the samples in $X$ that inherit from ancestral chromosome $a$ at site $\ell$, and similarly for $Y,U,V$. Then

$$\mathbb{E}\bigl[f_4(X,Y;U,V)\bigr]=\frac{1}{G}\sum_{\ell=1}^{G}\sum_{a}\mu(\ell)\bigl(F_X(a,\ell)-F_Y(a,\ell)\bigr)\bigl(F_U(a,\ell)-F_V(a,\ell)\bigr),$$

the sum running over all ancestral chromosomes.

(II) Equivalently, let $S_{xu\mid yv}(\ell)$ be the length (in generations) of the internal branch of the unrooted tree of $x,y,u,v$ at site $\ell$ if that tree has topology $xu\mid yv$, and $0$ otherwise. Then

$$\mathbb{E}\bigl[f_4(X,Y;U,V)\bigr]=\frac{1}{n_Xn_Yn_Un_V}\sum_{x,y,u,v}\frac{1}{G}\sum_{\ell=1}^{G}\mu(\ell)\bigl(S_{xu\mid yv}(\ell)-S_{xv\mid yu}(\ell)\bigr),$$

summing over $x\in X$, $y\in Y$, $u\in U$, $v\in V$, and

$$\operatorname{Var}\bigl[f_4(X,Y;U,V)\bigr]\le\frac{1}{n_Xn_Yn_Un_V}\sum_{x,y,u,v}\frac{1}{G^{2}}\sum_{\ell=1}^{G}\mu(\ell)\bigl(S_{xu\mid yv}(\ell)+S_{xv\mid yu}(\ell)\bigr).$$

So $f_4$ estimates, with variance of order $1/G$, a descriptive summary of the actual genealogies: the mutation-weighted excess of internal-branch length supporting $xu\mid yv$ over $xv\mid yu$. It vanishes in expectation whenever the two discordant topologies have equal total internal length, as under a tree of populations without gene flow, without assuming any population model.

## Expansion

A statistic linear in allele frequencies is an integral $\int\phi\,dM$ of a test function against the Poisson mutation measure $M$, and Campbell's theorem gives $\mathbb{E}\int\phi\,dM=\int\phi\,d\mu$ and $\operatorname{Cov}(\int\phi\,dM,\int\psi\,dM)=\int\phi\psi\,d\mu$ (Lemmas 1–2). A mutation on $a$ at $\ell$ raises $p_X(\ell)$ by $F_X(a,\ell)$; under infinite sites the product in $f_4$ only collects pairs of contributions from the same mutation, which gives (I). Summing over ancestors at a fixed site, $F_X-F_Y$ and $F_U-F_V$ are both non-zero only on the internal branch separating $\{x,u\}$ from $\{y,v\}$ or $\{x,v\}$ from $\{y,u\}$, with signs $+1$ and $-1$, which gives (II). This complements the model-based identity [$f_4$ in terms of expected coalescence times](../../../population-structure/coalescence-times-f-statistics-and-pca/f4-eq.md), which averages over a random genealogy instead of conditioning on the realized one.

## Depends on

- [Patterson's $f_4$ statistic](../../../population-structure/patterson-s-f-statistics/f4.md)

## Sources

- Peter L. Ralph, "An empirical approach to demographic inference with genomic data", *Theoretical Population Biology* 127 (2019), 91–101, <https://doi.org/10.1016/j.tpb.2019.03.005>; preprint arXiv:1505.05816, <https://doi.org/10.48550/arXiv.1505.05816>. Numbering of the arXiv version: Main results (Theorem 1), Section "A formal calculus of mutations on the ARG" (Definitions of paths and observable statistics, Lemmas 1–3).
