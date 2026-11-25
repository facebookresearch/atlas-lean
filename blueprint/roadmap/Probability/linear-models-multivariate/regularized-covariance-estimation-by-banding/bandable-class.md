# The bandable class $\mathcal U(\varepsilon_0, \alpha, C)$

For real numbers $\varepsilon_0, \alpha, C$, the class $\mathcal U(\varepsilon_0, \alpha, C)$ consists of the symmetric real $p \times p$ matrices $\Sigma = [\sigma_{ij}]$ with

$$\varepsilon_0 \|x\|^2 \le x^{\mathsf T} \Sigma x \le \varepsilon_0^{-1} \|x\|^2 \ \text{ for all } x \in \mathbb R^p \qquad\text{and}\qquad \max_j \sum_{i : |i - j| > k} |\sigma_{ij}| \le C k^{-\alpha} \text{ for all integers } k \ge 1,$$

with $0^{-1} = 0$. For $\varepsilon_0 > 0$ the first condition says that the eigenvalues of $\Sigma$ lie in $[\varepsilon_0, 1/\varepsilon_0]$, which is how Bickel and Levina state it; they take $\varepsilon_0, \alpha, C > 0$ and the decay condition for all $k > 0$. Bickel and Levina show that it contains the covariance matrices of stationary processes whose spectral density is bounded away from $0$ and $\infty$ and has a bounded derivative of order $m$, with $\alpha = m - 1$.

## Sources

- P. J. Bickel and E. Levina, "Regularized estimation of large covariance matrices", *Ann. Statist.* 36 (2008) 199–227, Section 3.1, equation (5).
