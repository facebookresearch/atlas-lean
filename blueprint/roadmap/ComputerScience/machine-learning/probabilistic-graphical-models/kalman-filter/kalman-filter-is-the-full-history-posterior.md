# The Kalman filter gives the conditional law given the whole observation history

Fix a horizon $N \ge 0$. Let $F_k \in \mathbb{R}^{n \times n}$, $G_k \in \mathbb{R}^{n \times r}$ and $Q_k \in \mathbb{R}^{r \times r}$ positive semidefinite for $0 \le k < N$, and $H_k \in \mathbb{R}^{n \times p}$ and $R_k \in \mathbb{R}^{p \times p}$ positive definite for $0 \le k \le N$, be deterministic matrices. Consider the linear Gaussian signal model

$$x_{k+1} = F_k x_k + G_k w_k \quad (0 \le k < N), \qquad z_k = H_k^\top x_k + v_k \quad (0 \le k \le N),$$

where $x_0 \sim N(\bar x_0, P_0)$ with $P_0$ positive semidefinite, $w_k \sim N(0, Q_k)$, $v_k \sim N(0, R_k)$, and $x_0, w_0, \dots, w_{N-1}, v_0, \dots, v_N$ are jointly Gaussian and mutually independent. Write $Z_k = (z_0, \dots, z_k)$, with $Z_{-1}$ empty, so conditioning on $Z_{-1}$ means no conditioning. Define $\hat x_{0|-1} = \bar x_0$, $\Sigma_{0|-1} = P_0$, the measurement update for $0 \le k \le N$

$$\hat x_{k|k} = \hat x_{k|k-1} + \Sigma_{k|k-1} H_k (H_k^\top \Sigma_{k|k-1} H_k + R_k)^{-1} (z_k - H_k^\top \hat x_{k|k-1}),$$

$$\Sigma_{k|k} = \Sigma_{k|k-1} - \Sigma_{k|k-1} H_k (H_k^\top \Sigma_{k|k-1} H_k + R_k)^{-1} H_k^\top \Sigma_{k|k-1},$$

and the time update for $0 \le k < N$

$$\hat x_{k+1|k} = F_k \hat x_{k|k}, \qquad \Sigma_{k+1|k} = F_k \Sigma_{k|k} F_k^\top + G_k Q_k G_k^\top .$$

The inverted matrices are positive definite because $R_k$ is.

Then for every $k \le N$:

1. the conditional distribution of $x_k$ given $Z_{k-1}$ is $N(\hat x_{k|k-1}(Z_{k-1}), \Sigma_{k|k-1})$, and the conditional distribution of $x_k$ given $Z_k$ is $N(\hat x_{k|k}(Z_k), \Sigma_{k|k})$, for almost every value of the observation history under its law;
2. in particular $\hat x_{k|k} = E[x_k \mid Z_k]$ almost surely, so $\hat x_{k|k}(Z_k)$ minimizes $E\|x_k - g(Z_k)\|^2$ over measurable $g$ and is almost surely the unique minimizer; and $\Sigma_{k|k}$ does not depend on the observations.

Because the whole family is jointly Gaussian, $(x_k, Z_k)$ is a Gaussian vector, and its conditional law is the Gaussian obtained by Schur complements. The proof identifies these batch parameters with the recursion by induction on $k$. Given $Z_{k-1}$, the pair $(x_k, z_k)$ is Gaussian with mean $(\hat x_{k|k-1}, H_k^\top \hat x_{k|k-1})$ and covariance $\begin{bmatrix} \Sigma_{k|k-1} & \Sigma_{k|k-1} H_k \\ H_k^\top \Sigma_{k|k-1} & H_k^\top \Sigma_{k|k-1} H_k + R_k \end{bmatrix}$. Conditioning further on $z_k$ gives the measurement update. For $k<N$, the noise $w_k$, independent of $(x_k, Z_k)$, gives the time update. In the existing one-step convention the observation matrix is $H_k^\top$ and the additive process covariance is $G_kQ_kG_k^\top$. The covariance of the stacked observations is positive definite: their independent measurement noises contribute the positive definite block diagonal matrix with blocks $R_0,\dots,R_k$, and the remaining covariance is positive semidefinite.

For the MMSE assertion, apply conditional orthogonality in each coordinate and sum to obtain, with $m=E[x_k\mid Z_k]$,

$$E\|x_k-g(Z_k)\|^2=E\|x_k-m\|^2+E\|m-g(Z_k)\|^2.$$

This holds for every square-integrable competitor. A measurable competitor with infinite squared-error cost cannot minimize the finite Gaussian cost; finite error implies square-integrability of the competitor. Equality therefore holds precisely when $g(Z_k)=m$ almost surely. Costs are nonnegative expectations, allowed to be infinite.

**Known inputs and noise means.** If $x_{k+1} = F_k x_k + B_k u_k + G_k w_k$ for $0 \le k < N$ with deterministic matrices $B_k\in\mathbb R^{n\times d}$ and known deterministic inputs $u_k\in\mathbb R^d$, retaining all the independence assumptions, $w_k \sim N(\mu_k, Q_k)$ and $v_k \sim N(\nu_k, R_k)$, the same conclusions hold with $\hat x_{k+1|k} = F_k \hat x_{k|k} + B_k u_k + G_k \mu_k$ and with $z_k - \nu_k - H_k^\top \hat x_{k|k-1}$ as the innovation. Indeed, subtracting the deterministic mean trajectory reduces the model to the zero-mean case. The covariance recursion is unchanged. Here $\mu_k$ is specified for $0\le k<N$ and $\nu_k$ for $0\le k\le N$.

## Proof depends on

- [Gaussian conditioning (Schur complement)](../../../../Probability/distributions/continuous/gaussian-conditioning/cond-distrib-multivariate-gaussian.md): the Gaussian conditional-law theorem used to identify the batch posterior

- [One filter step is the exact posterior](cond-distrib-step.md): one predict-and-update step as an exact conditional law, used in the induction step
- [The conditional mean minimizes the expected squared error](../../../../Probability/foundations/conditional-expectation-as-the-best-predictor/integral-sq-sub-cond-exp-le.md): the conditional mean minimizes the mean squared error

## Sources

- B. D. O. Anderson and J. B. Moore, *Optimal Filtering*, Prentice-Hall, 1979, <https://users.cecs.anu.edu.au/~john/papers/BOOK/B02.PDF>, Section 3.1, pp. 36–44: the signal model (1.1)–(1.2) with independent zero-mean Gaussian white noises and Gaussian initial state (1.4), the filter equations (1.6)–(1.12) and their first-principles derivation by repeated Gaussian conditioning (pp. 39–40), property 5 (the conditional density of $x_k$ is Gaussian with the filter's mean and covariance, p. 43) and the footnote on p. 39 ($R_k$ positive definite guarantees the inverse); known external inputs: Problem 1.1, pp. 44–45.
