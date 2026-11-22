# EKI output covariance

The empirical covariance of the forward-mapped ensemble, as a linear map on the data space:

$$
C^{pp}(u)\, d = \frac1J \sum_{k=1}^J \big\langle G(u^{(k)}) - \overline G, d \big\rangle \, (G(u^{(k)}) - \overline G) .
$$

Here $u^{(1)}, \dots, u^{(J)}$ is the ensemble, $G$ the forward map into a real inner product space and $\overline G$ the ensemble mean of the images; for $J = 0$ the map is $0$.

## Sources

- Claudia Schillings and Andrew M. Stuart, *Analysis of the ensemble Kalman filter for inverse problems*, SIAM J. Numer. Anal. 55 (2017), no. 3, 1264–1290, DOI 10.1137/16M105959X; arXiv:1602.02020, equation (5).
- Marco A. Iglesias, Kody J. H. Law and Andrew M. Stuart, *Ensemble Kalman methods for inverse problems*, Inverse Problems 29 (2013), no. 4, 045001, DOI 10.1088/0266-5611/29/4/045001; arXiv:1209.2736, equation (21).
