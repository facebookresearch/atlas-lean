# Identity $PVP = P$ for the residual-forming matrix

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals with [phenotypic covariance](v.md) $V$, and let $X$ be a real $n \times p$ matrix of full column rank. Then the [residual-forming matrix](proj.md) satisfies

$$P V P = P.$$

Together with $PX = 0$, this means that under the null model $y = X\beta + \varepsilon$ with $\operatorname{Cov} \varepsilon = V$, the score $x^\top P y = x^\top P \varepsilon$ of a SNP $x$ has variance $x^\top P V P x = x^\top P x$.
