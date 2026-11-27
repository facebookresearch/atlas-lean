# Unified Q + K mixed model for association mapping

Let $y \in \mathbb{R}^n$ be phenotypes of $n$ individuals. The unified mixed model for association mapping in a sample with both population structure and familial relatedness is

$$y = X\beta + S\alpha + Qv + Zu + e,$$

where

- $\beta$ is a vector of fixed non-marker effects with design $X$;
- $\alpha$ is the fixed effect of the tested marker, with design $S$ (genotype codes);
- $v$ is a vector of fixed effects of population structure, with $Q$ the $n \times k$ matrix of estimated membership proportions in $k$ subpopulations;
- $u$ is the random polygenic background effect, $Z$ its incidence matrix, with $\operatorname{Var}(u) = 2K\,V_g$, where $K$ is the matrix of relative kinship coefficients and $V_g$ the genetic variance;
- $e$ is the residual, $\operatorname{Var}(e) = R\,V_R$ (with $R = I$ in the original analyses), independent of $u$.

Thus $\operatorname{Var}(y) = V = 2ZKZ^\top V_g + R V_R$. For known variance components, the fixed effects $(\beta, \alpha, v)$ are estimated by generalized least squares with weight $V^{-1}$, equivalently from Henderson's mixed-model equations, and the marker is tested through $H_0: \alpha = 0$. Dropping $Qv$ gives the K model, dropping $Zu$ gives the Q model (ordinary least squares), and dropping both gives the naive single-marker test.

## Depends on

- [Marginal law of the mixed-model response](../../quantitative-genetics/linear-mixed-models-and-blup/map-mixed-model-response.md)

## Expansion

The kinship term absorbs the fine-scale covariance among relatives that a few fixed structure covariates cannot capture, while $Qv$ absorbs coarse mean differences between subpopulations. Because $\alpha$ enters only the mean, the generalized least-squares estimator $\hat\theta = (W^\top V^{-1} W)^{-1} W^\top V^{-1} y$ with $W = [X\ S\ Q]$ is the best linear unbiased estimator of $\theta = (\beta, \alpha, v)$ given $V$, and Wald or $F$ tests of $\alpha$ use the corresponding block of $(W^\top V^{-1} W)^{-1}$. The [EMMA reduction](emma-spectral-reduction-of-ml-and-reml.md) is an exact algorithm for estimating $V_g$ and $V_R$ in this model.

## Sources

- J. Yu, G. Pressoir, W. H. Briggs, I. Vroh Bi, M. Yamasaki, J. F. Doebley, M. D. McMullen, B. S. Gaut, D. M. Nielsen, J. B. Holland, S. Kresovich and E. S. Buckler, "A unified mixed-model method for association mapping that accounts for multiple levels of relatedness", Nature Genetics 38 (2006), 203–208, <https://doi.org/10.1038/ng1702>.
