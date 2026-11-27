# EKI cross-covariance applied to a vector

$$
C^{up}(u)\, d = \frac1J \sum_{k=1}^J \big\langle G(u^{(k)}) - \overline G, d \big\rangle \, (u^{(k)} - \overline u),
$$

for an ensemble $u^{(1)}, \dots, u^{(J)}$ in a real vector space $X$, a forward map $G$ into a real inner product space $F$ and $d \in F$, where $\overline u$ and $\overline G$ are the ensemble means of the particles and of their images under $G$; for $J = 0$ it is $0$.
This is the empirical covariance $\frac1J \sum_k (u^{(k)} - \overline u) \otimes (G(u^{(k)}) - \overline G)$ applied
to $d$.

## Sources

- Claudia Schillings and Andrew M. Stuart, *Analysis of the ensemble Kalman filter for inverse problems*, SIAM J. Numer. Anal. 55 (2017), no. 3, 1264–1290, DOI 10.1137/16M105959X; arXiv:1602.02020, equation (5).
- Marco A. Iglesias, Kody J. H. Law and Andrew M. Stuart, *Ensemble Kalman methods for inverse problems*, Inverse Problems 29 (2013), no. 4, 045001, DOI 10.1088/0266-5611/29/4/045001; arXiv:1209.2736, equations (20) and (22).
