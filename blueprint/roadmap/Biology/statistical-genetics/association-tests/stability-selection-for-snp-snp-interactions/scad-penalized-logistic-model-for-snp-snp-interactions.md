# SCAD-penalized logistic model for SNP-SNP interactions

**Model.** For $n$ case-control subjects with disease status $y_i\in\{0,1\}$ and genotype codes $x_{i1},\dots,x_{im}$ at $m$ SNPs, the pairwise-interaction logistic model is

$$y_i\sim\mathrm{Bernoulli}(\pi_i),\qquad \log\frac{\pi_i}{1-\pi_i}=\beta_0+\sum_{j=1}^m\beta_jx_{ij}+\sum_{j<k}\xi_{jk}\,x_{ij}x_{ik},$$

with $p=m+m(m-1)/2$ candidate main-effect and interaction coefficients $\theta=(\beta,\xi)$, typically $p\gg n$. Sparse estimates minimize the penalized deviance

$$l_p(\theta)=-2\log L(\theta)+\sum_{j=1}^p p_\lambda(|\theta_j|).$$

The lasso uses $p_\lambda(t)=\lambda t$. The SCAD penalty is defined for $t>0$ by its derivative

$$p'_\lambda(t)=\lambda\Big\{\mathbf 1(t\le\lambda)+\frac{(a\lambda-t)_+}{(a-1)\lambda}\,\mathbf 1(t>\lambda)\Big\},\qquad a>2,$$

so it equals the lasso near zero, tapers linearly on $(\lambda,a\lambda]$ and is constant beyond $a\lambda$.

**Property.** Because $p'_\lambda(t)=0$ for $t>a\lambda$, large coefficients are not shrunk, which removes the lasso's bias on strong effects, while the singularity at zero still sets small coefficients exactly to zero.

## Depends on

- [Lasso objective](../../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/lasso.md)

## Expansion

The penalty integrates to $p_\lambda(t)=\lambda t$ on $[0,\lambda]$, $(2a\lambda t-t^2-\lambda^2)/(2(a-1))$ on $(\lambda,a\lambda]$ and $(a+1)\lambda^2/2$ beyond, which is continuous, nonconvex and bounded. For a single orthogonal coordinate the resulting thresholding rule is soft thresholding for $|z|\le2\lambda$, a linear interpolation on $(2\lambda,a\lambda]$ and the identity beyond $a\lambda$. The source fits the model by coordinate descent (a modified nonconvex-penalty solver for SCAD, a lasso solver for comparison); the explicit interaction terms make the number of candidates grow quadratically in $m$, which is what makes selection error control necessary. The source prefers SCAD to the lasso because of its oracle property (Fan and Li 2001, Theorem 2): under the conditions stated there, the penalized estimator selects the true support with probability tending to one and estimates the nonzero coefficients as efficiently as if that support were known.

## Sources

- Gou J, Zhao Y, Wei Y, Wu C, Zhang R, Qiu Y, Zeng P, Tan W, Yu D, Wu T, Hu Z, Lin D, Shen H, Chen F. Stability SCAD: a powerful approach to detect interactions in large-scale genomic study. *BMC Bioinformatics* 15:62 (2014). <https://doi.org/10.1186/1471-2105-15-62> (PMCID: PMC3984751). Eqs. (1)-(2) and the penalty definitions in Methods.
- J. Fan and R. Li, "Variable selection via nonconcave penalized likelihood and its oracle properties", *Journal of the American Statistical Association* 96 (2001), 1348–1360, Theorem 2. <https://doi.org/10.1198/016214501753382273>
