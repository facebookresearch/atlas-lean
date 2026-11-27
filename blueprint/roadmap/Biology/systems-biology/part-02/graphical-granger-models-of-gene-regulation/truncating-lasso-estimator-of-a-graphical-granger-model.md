# Truncating lasso estimator of a graphical Granger model

**Model.** Let $X^t = (X^t_1,\dots,X^t_p)^\top$, $t = 1,\dots,T$, be a $p$-variate time series (expression of $p$ genes), observed in $n$ independent replicates, with $\mathcal{X}^t$ the $n \times p$ design matrix at time $t$ and $\mathcal{X}^t_j$ its $j$-th column. The graphical Granger model of order $d$ is the vector autoregression

$$X^T_i = \sum_{t=1}^{d} \sum_{j=1}^{p} A^t_{ij} X^{T-t}_j + \varepsilon_i,\qquad i = 1,\dots,p,$$

and $X_j$ is a Granger cause of $X_i$ at lag $t$ when $A^t_{ij} \ne 0$. This is a directed acyclic graph on $T \times p$ nodes ordered by time, so the coefficients can be estimated by $p$ separate penalized regressions.

**Estimator.** For a tuning parameter $\lambda > 0$, an allowed false-negative rate $\beta \in [0,1)$, a large constant $M$, and nonnegative weights $w^t_j$ (all equal to $1$ for the lasso, inverse initial lasso estimates for the adaptive lasso), the truncating lasso estimate for gene $i$ minimizes, over $\theta^1,\dots,\theta^d \in \mathbb{R}^p$,

$$\frac{1}{n}\Big\| \mathcal{X}^T_i - \sum_{t=1}^{d} \mathcal{X}^{T-t}\theta^t \Big\|_2^2 + \lambda \sum_{t=1}^{d} \Psi^t \sum_{j=1}^{p} |\theta^t_j|\, w^t_j,$$

$$\Psi^1 = 1,\qquad \Psi^t = M^{\mathbb{1}\{\|A^{(t-1)}\|_0 < p^2\beta/(T-t)\}}\quad (t \ge 2),$$

where $A^{(t-1)}$ is the estimated adjacency matrix at lag $t-1$ and $\|\cdot\|_0$ counts nonzero entries. Once some lag carries fewer than $p^2\beta/(T-t)$ edges, every later lag is penalized by the factor $M$ and is driven to zero, and the first such lag minus one is the estimated order $\hat d$.

## Expansion

The plain lasso on all $p(T-1)$ lagged covariates both ignores the unknown order and tends to select the same regulator at several lags, which is hard to interpret; the group lasso fixes the latter by averaging over lags but loses the lag and the sign of each effect. The truncation encodes the assumption that the number of true edges decreases with the lag: when a lag looks nearly empty, all longer lags are switched off. The objective is solved by block-relaxation over the $\theta^t$, each block being a weighted lasso with the current $\Psi^t$.

## Sources

- Shojaie A, Michailidis G, "Discovering graphical Granger causality using the truncating lasso penalty", Bioinformatics (2010), Section 2.2 (Eq. (6)) and Section 2.3 (Eqs. (7)–(8)), <https://doi.org/10.1093/bioinformatics/btq377>, PMCID PMC2935442.
