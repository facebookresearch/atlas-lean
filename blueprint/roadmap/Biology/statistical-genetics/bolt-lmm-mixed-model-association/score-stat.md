# Score statistic for one SNP

Let $(K, \sigma_g^2, \sigma_e^2)$ be [variance components](model.md) on $n$ individuals, let $X$ be a real $n \times p$ matrix with [residual-forming matrix](proj.md) $P$, and let $x, y \in \mathbb{R}^n$. The score statistic of the SNP $x$ is

$$T = \frac{(x^\top P y)^2}{x^\top P x},$$

with the convention $a/0 = 0$. The denominator is positive when $X$ has full column rank and $x$ is not in the column space of $X$ ([positivity of the information](info-pos.md)).
