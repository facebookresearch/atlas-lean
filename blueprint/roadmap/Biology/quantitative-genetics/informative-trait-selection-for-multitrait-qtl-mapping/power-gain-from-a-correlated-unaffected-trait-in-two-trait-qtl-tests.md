# Power gain from a correlated unaffected trait in two-trait QTL tests

**Setting.** In a backcross or recombinant inbred population, a marker splits $n$ individuals into two genotype groups of sizes $n_1,n_2$. Traits $y=(y_1,\dots,y_p)$ are multivariate normal within groups with common covariance $\Sigma$ and genotype-group mean difference $\delta\in\mathbb R^p$ (the QTL effects). The multitrait test of $H_0:\delta=0$ uses Hotelling's statistic $T^2_{y_1,\dots,y_k}$ on the first $k$ traits, and the contribution of an added trait is assessed by

$$F_{y_{k+1}\mid y_1,\dots,y_k}=(n-k-2)\,\frac{T^2_{y_1,\dots,y_{k+1}}-T^2_{y_1,\dots,y_k}}{T^2_{y_1,\dots,y_k}+n-2},\qquad T^2_{\emptyset}=0,$$

which under the null of no additional information is $F_{1,\,n-k-2}$-distributed.

**Proposition 1.** If a QTL has a nonzero effect on one trait and no effect on another, then the power of the joint two-trait test to detect the QTL tends to $100\%$ as the residual correlation $\rho$ between the two traits tends to $1$ or $-1$.

Concretely, with $\delta=(\delta_1,0)^{\top}$ and $\Sigma=\begin{pmatrix}\sigma_1^2&\rho\sigma_1\sigma_2\\ \rho\sigma_1\sigma_2&\sigma_2^2\end{pmatrix}$, the noncentrality of the two-trait test is

$$\lambda_2=\frac{n_1n_2}{n}\,\delta^{\top}\Sigma^{-1}\delta=\frac{n_1n_2}{n}\cdot\frac{\delta_1^2}{\sigma_1^2(1-\rho^2)}=\frac{\lambda_1}{1-\rho^2},$$

where $\lambda_1=\frac{n_1n_2}{n}\delta_1^2/\sigma_1^2$ is the noncentrality of the single-trait test on $y_1$. Since $\lambda_2\to\infty$ as $|\rho|\to1$ with fixed degrees of freedom, the power tends to one.

## Depends on

- [Snedecor's F distribution](../../../Probability/linear-models-multivariate/student-s-t-and-snedecor-s-f-distributions/snedecor-fmeasure.md)

## Expansion

The unaffected trait $y_2$ carries no signal itself but measures the residual noise of $y_1$: regressing out $y_2$ leaves $y_1\mid y_2$ with the same mean difference $\delta_1$ and residual variance $\sigma_1^2(1-\rho^2)$. Inverting the $2\times2$ covariance gives $(\Sigma^{-1})_{11}=1/(\sigma_1^2(1-\rho^2))$, which yields the noncentrality formula. The conditional $F$ statistic compares $T^2$ with and without the added trait, so traits that do not raise $T^2$ enough are redundant; when traits are chosen by maximizing their contribution, that $F$ reference distribution no longer holds and significance is assessed by permuting genotypes. Conversely, adding a trait that is uncorrelated with the others and unaffected by the QTL costs a degree of freedom without increasing $\lambda$, lowering power, which motivates selecting informative traits rather than analyzing all of them.

## Sources

- Cheng R, Borevitz J, Doerge RW, "Selecting informative traits for multivariate quantitative trait locus mapping helps to gain optimal power", Genetics 195(3):683-691, Equations (1)-(2) and Proposition 1, <https://doi.org/10.1534/genetics.113.155937>, PMCID PMC3813856.
