# Empirical covariance of mean coalescence times across genomic windows

**Setting.** As in the [genealogical reading of $f_4$](genealogical-interpretation-of-the-f4-statistic.md), the genealogy is fixed and mutations form a Poisson process under the infinite-sites model with per-site rate $\mu_\ell$. For two pairs of sampled chromosomes $(x_1,x_2)$ and $(y_1,y_2)$ let $t_x(\ell)$ be the number of ancestors from whom exactly one of $x_1,x_2$ inherits at site $\ell$ (the tree length between them), and likewise $t_y(\ell)$. Split the genome of $G$ sites into $n$ disjoint windows $W_1,\dots,W_n$ of equal length $|W|=G/n$ that cover it, and set

$$\overline{\mu t}_{k,x}=\frac{1}{|W_k|}\sum_{\ell\in W_k}\mu_\ell\,t_x(\ell), \qquad \overline{\overline{\mu t}}_x=\frac{1}{G}\sum_{\ell=1}^{G}\mu_\ell\,t_x(\ell),$$

and similarly for $y$.

**Theorem 2.** Let $N_k(x)$ be the number of mutations in $W_k$ distinguishing $x_1$ from $x_2$, $N_k(y)$ the same for $y_1,y_2$, and $N_k(x,y)$ the number that do both. Put $Z_{jk}=N_j(x)N_k(y)/(|W_j||W_k|)$ for $j\neq k$ and $Z_{jj}=(N_j(x)N_j(y)-N_j(x,y))/|W_j|^2$. Then

$$C_{x,y}=\frac{1}{n}\sum_{k=1}^{n}\Bigl(Z_{kk}-\frac{1}{n}\sum_{j=1}^{n}Z_{jk}\Bigr)$$

satisfies

$$\mathbb{E}\bigl[C_{x,y}\bigr]=\frac{1}{n}\sum_{k=1}^{n}\bigl(\overline{\mu t}_{k,x}-\overline{\overline{\mu t}}_x\bigr)\bigl(\overline{\mu t}_{k,y}-\overline{\overline{\mu t}}_y\bigr),$$

the empirical covariance of the window means, centred at the genome means (which here equal the averages of the window means).

So the covariance across windows of mean (mutation-scaled) times to the most recent common ancestor of two pairs is estimable without a demographic model. By contrast, the variance of single-site coalescence times cannot be estimated without modelling recombination-induced dependence between sites.

## Expansion

$N_k(x)$ is the Poisson integral of the path indicator of $x_1,x_2$ restricted to $W_k$, so $\mathbb{E}N_k(x)=|W_k|\overline{\mu t}_{k,x}$. For $j\neq k$ the counts are independent and $\mathbb{E}Z_{jk}$ is the product of the window means. Within a window, $N_j(x)$ and $N_j(y)$ share the mutations falling on branches separating both pairs; their covariance is exactly $\mathbb{E}N_j(x,y)$ by Campbell's covariance formula, so subtracting $N_j(x,y)$ removes the Poisson noise term and leaves the product of means. Averaging the diagonal minus the row averages yields the empirical covariance. For the variance, the general moment formula for Poisson integrals (Lemma 3) expands $\operatorname{Var}[C_{x,y}]$ into terms of several orders in the window means; the source's appendix keeps only those of order $\epsilon^3/(n|W|)$, with $\epsilon=\max_k\max(\overline{\mu t}_{k,x},\overline{\mu t}_{k,y})$, as an order-of-magnitude estimate for windows carrying many mutations ($\epsilon|W|$ large). It is not a bound in general: for $n=2$, all window means equal to $\epsilon$ and pairs whose separating paths share no branch, $\operatorname{Var}[C_{x,y}]=\epsilon^2/(4|W|^2)$, which exceeds $\epsilon^3/(2|W|)$ when $\epsilon|W|<1/2$.

## Depends on

- [Genealogical interpretation of the $f_4$ statistic](genealogical-interpretation-of-the-f4-statistic.md)

## Sources

- Peter L. Ralph, "An empirical approach to demographic inference with genomic data", *Theoretical Population Biology* 127 (2019), 91–101, <https://doi.org/10.1016/j.tpb.2019.03.005>; preprint arXiv:1505.05816, <https://doi.org/10.48550/arXiv.1505.05816>. Numbering of the arXiv version: Main results (Theorem 2), Section "A formal calculus of mutations on the ARG" (Lemmas 1–3), appendix on the variance of $C_{x,y}$.
