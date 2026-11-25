# One step of ensemble Kalman inversion

For an ensemble $u = (u^{(1)}, \dots, u^{(J)})$, a forward map $G$, a noise covariance $\Gamma$ and
(possibly perturbed) data $y^{(j)}$,

$$
u^{(j)} \mapsto u^{(j)} + C^{up}(u) \big(C^{pp}(u) + \Gamma\big)^{-1} \big(y^{(j)} - G(u^{(j)})\big),
$$

with the [cross-covariance](cross-cov.md) $C^{up}$ and [output covariance](output-cov.md) $C^{pp}$ of the
ensemble, for a real vector space $X$ of unknowns, a real inner product space $F$ of data and a linear map $\Gamma$ on $F$. The inverse $(C^{pp} + \Gamma)^{-1}$ is the inverse in the ring of linear maps on $F$, read as $0$ when $C^{pp} + \Gamma$ is not invertible; it is invertible for instance when $\Gamma$ is positive definite on a finite-dimensional
data space. Schillings and Stuart's version replaces $\Gamma$ by $h^{-1} \Gamma$.

## Sources

- Marco A. Iglesias, Kody J. H. Law and Andrew M. Stuart, *Ensemble Kalman methods for inverse problems*, Inverse Problems 29 (2013), no. 4, 045001, DOI 10.1088/0266-5611/29/4/045001; arXiv:1209.2736, equation (25).
- Claudia Schillings and Andrew M. Stuart, *Analysis of the ensemble Kalman filter for inverse problems*, SIAM J. Numer. Anal. 55 (2017), no. 3, 1264–1290, DOI 10.1137/16M105959X; arXiv:1602.02020, equations (4) and (5).
