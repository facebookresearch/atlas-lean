# Second-moment model for summary-statistic imputation

Let $P$ be a measure on a measurable space $\Omega$ and let $\iota$ be a set of typed markers. A second-moment imputation model consists of real functions $z_t$ (the statistic of the untyped target marker) and $z_{o,i}$ for $i \in \iota$ (the statistics of the typed markers) on $\Omega$, all square integrable with respect to $P$, together with a real $\iota \times \iota$ matrix $\Sigma_{oo}$, a vector $\Sigma_{ot} \in \mathbb{R}^\iota$ and a real number $\Sigma_{tt}$ such that for all $i, j \in \iota$

- $\int z_{o,i}\, z_{o,j} \, dP = (\Sigma_{oo})_{ij}$;
- $\int z_t\, z_{o,i} \, dP = (\Sigma_{ot})_i$;
- $\int z_t^2 \, dP = \Sigma_{tt}$.

When $P$ is a probability measure and the statistics are centred, these are the LD covariances of the ImpG null model.
