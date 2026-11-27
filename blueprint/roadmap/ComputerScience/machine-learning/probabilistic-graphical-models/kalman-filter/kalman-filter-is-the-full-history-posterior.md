# The Kalman filter gives the conditional law given the whole observation history

Fix a horizon $N \ge 0$. Let $F_k \in \mathbb{R}^{n \times n}$, $G_k \in \mathbb{R}^{n \times r}$ and $Q_k \in \mathbb{R}^{r \times r}$ positive semidefinite for $0 \le k < N$, and $H_k \in \mathbb{R}^{n \times p}$ and $R_k \in \mathbb{R}^{p \times p}$ positive definite for $0 \le k \le N$, be deterministic matrices, and let $\bar x_0 \in \mathbb{R}^n$ and $P_0 \in \mathbb{R}^{n \times n}$ positive semidefinite. On a probability space, consider random vectors $x_k \in \mathbb{R}^n$, $w_k \in \mathbb{R}^r$ and $v_k, z_k \in \mathbb{R}^p$ forming the linear Gaussian signal model

$$x_{k+1} = F_k x_k + G_k w_k \quad (0 \le k < N), \qquad z_k = H_k^\top x_k + v_k \quad (0 \le k \le N),$$

where $x_0, w_0, \dots, w_{N-1}, v_0, \dots, v_N$ are measurable and mutually independent, with $x_0 \sim N(\bar x_0, P_0)$, $w_k \sim N(0, Q_k)$ and $v_k \sim N(0, R_k)$: their joint law is the product of these Gaussian laws. Write $Z_k = (z_0, \dots, z_k)$, with $Z_{-1}$ empty, so conditioning on $Z_{-1}$ means no conditioning. Define $\hat x_{0|-1} = \bar x_0$, $\Sigma_{0|-1} = P_0$, the measurement update for $0 \le k \le N$

$$\hat x_{k|k} = \hat x_{k|k-1} + \Sigma_{k|k-1} H_k (H_k^\top \Sigma_{k|k-1} H_k + R_k)^{-1} (z_k - H_k^\top \hat x_{k|k-1}),$$

$$\Sigma_{k|k} = \Sigma_{k|k-1} - \Sigma_{k|k-1} H_k (H_k^\top \Sigma_{k|k-1} H_k + R_k)^{-1} H_k^\top \Sigma_{k|k-1},$$

and the time update for $0 \le k < N$

$$\hat x_{k+1|k} = F_k \hat x_{k|k}, \qquad \Sigma_{k+1|k} = F_k \Sigma_{k|k} F_k^\top + G_k Q_k G_k^\top ,$$

so that $\hat x_{k|k-1}$ is a function of $Z_{k-1}$ and $\hat x_{k|k}$ a function of $Z_k$. The inverted matrices are positive definite because $R_k$ is.

Then for every $k \le N$:

1. the conditional distribution of $x_k$ given $Z_{k-1}$ is $N(\hat x_{k|k-1}(Z_{k-1}), \Sigma_{k|k-1})$, for almost every value of $Z_{k-1}$ under its law, and the conditional distribution of $x_k$ given $Z_k$ is $N(\hat x_{k|k}(Z_k), \Sigma_{k|k})$, for almost every value of $Z_k$ under its law;
2. $\Sigma_{k|k}$ does not depend on the observations;
3. $\hat x_{k|k}(Z_k) = E[x_k \mid Z_k]$ almost surely;
4. for every measurable $g$, $E\|x_k - \hat x_{k|k}(Z_k)\|^2 \le E\|x_k - g(Z_k)\|^2$, with equality if and only if $g(Z_k) = \hat x_{k|k}(Z_k)$ almost surely. These costs are expectations of nonnegative random variables, allowed to be infinite.

## Proof sketch

By induction on $k$, the conditional law of $x_k$ given $Z_{k-1}$ is $N(\hat x_{k|k-1}(Z_{k-1}), \Sigma_{k|k-1})$. For $k = 0$ this is the law of $x_0$. Given this for some $k$, the noise $v_k$ is independent of $(Z_{k-1}, x_k)$, which is a function of $x_0$, of $w_j$ for $j < k$ and of $v_j$ for $j < k$. So, given $Z_{k-1}$, the pair $(x_k, z_k)$ is Gaussian with mean $(\hat x_{k|k-1}, H_k^\top \hat x_{k|k-1})$ and covariance $\begin{bmatrix} \Sigma_{k|k-1} & \Sigma_{k|k-1} H_k \\ H_k^\top \Sigma_{k|k-1} & H_k^\top \Sigma_{k|k-1} H_k + R_k \end{bmatrix}$, and conditioning further on $z_k$ by the Schur-complement formula gives the measurement update. For $k < N$, the noise $w_k$ is independent of $(Z_k, x_k)$, so given $Z_k$ the vector $x_{k+1} = F_k x_k + G_k w_k$ is Gaussian with the time-updated mean and covariance. The covariances never involve the observations.

For the mean squared error, condition on $Z_k$: for a fixed vector $c$ and $x \sim N(m, \Sigma)$, $E\|x - c\|^2 = E\|x - m\|^2 + \|m - c\|^2$. Integrating over the law of $Z_k$, with $m = \hat x_{k|k}(Z_k)$ and $c = g(Z_k)$,

$$E\|x_k-g(Z_k)\|^2=E\|x_k-\hat x_{k|k}(Z_k)\|^2+E\|\hat x_{k|k}(Z_k)-g(Z_k)\|^2,$$

in $[0, \infty]$, where the first term on the right is finite. Equality with $E\|x_k-\hat x_{k|k}(Z_k)\|^2$ therefore holds precisely when $g(Z_k)=\hat x_{k|k}(Z_k)$ almost surely. The conditional mean of $N(\hat x_{k|k}(Z_k), \Sigma_{k|k})$ is $\hat x_{k|k}(Z_k)$, which gives part 3.

## Remarks

If $x_{k+1} = F_k x_k + B_k u_k + G_k w_k$ for $0 \le k < N$ with deterministic matrices $B_k\in\mathbb R^{n\times d}$ and known deterministic inputs $u_k\in\mathbb R^d$, retaining all the independence assumptions, $w_k \sim N(\mu_k, Q_k)$ and $v_k \sim N(\nu_k, R_k)$, the same conclusions hold with $\hat x_{k+1|k} = F_k \hat x_{k|k} + B_k u_k + G_k \mu_k$ and with $z_k - \nu_k - H_k^\top \hat x_{k|k-1}$ as the innovation. Indeed, subtracting the deterministic mean trajectory reduces the model to the zero-mean case. The covariance recursion is unchanged. Here $\mu_k$ is specified for $0\le k<N$ and $\nu_k$ for $0\le k\le N$.

## Informally uses

- [One filter step is the exact posterior](cond-distrib-step.md): one predict-and-update step as an exact conditional law, which the source applies conditionally on the past observations
- [The conditional mean minimizes the expected squared error](../../../../Probability/foundations/conditional-expectation-as-the-best-predictor/integral-sq-sub-cond-exp-le.md): the conditional mean minimizes the mean squared error

## Sources

- B. D. O. Anderson and J. B. Moore, *Optimal Filtering*, Prentice-Hall, 1979, <https://users.cecs.anu.edu.au/~john/papers/BOOK/B02.PDF>, Section 3.1, pp. 36–44: the signal model (1.1)–(1.2) with independent zero-mean Gaussian white noises and Gaussian initial state (1.4), the filter equations (1.6)–(1.12) and their first-principles derivation by repeated Gaussian conditioning (pp. 39–40), property 2 (the error covariance $\Sigma_{k|k-1}$ and the gain do not depend on the measurements, p. 41), property 5 (the conditional density of $x_k$ is Gaussian with the filter's mean and covariance, p. 43) and the footnote on p. 39 ($R_k$ positive definite guarantees the inverse); known external inputs: Problem 1.1, pp. 44–45.
