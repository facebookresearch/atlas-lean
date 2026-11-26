# Monotonicity and limits of $R_0$ in the infected dispersal rate

In the [SIS patch model](sis-patch-model-and-its-basic-reproduction-number.md), assume $\beta_j, \gamma_j \ge 0$, $d_S, d_I > 0$, $L$ irreducible and quasi-positive with positive normalized null vector $\alpha$, and the $\gamma_j$ not all zero (use the conventions $\beta_j/\gamma_j = \infty$ if $\gamma_j = 0 < \beta_j$ and $\beta_j/\gamma_j = 0$ if $\beta_j = \gamma_j = 0$). Regard $R_0 = R_0(d_I)$ as a function of $d_I \in (0, \infty)$. Then

1. $\displaystyle \min_{j}\frac{\beta_j}{\gamma_j} \le R_0(d_I) \le \max_j \frac{\beta_j}{\gamma_j}$ for all $d_I > 0$;
2. if $(\beta_1, \dots, \beta_n)$ is not a multiple of $(\gamma_1, \dots, \gamma_n)$, then $R_0(d_I)$ is strictly decreasing on $(0, \infty)$;
3. the limits are

$$\lim_{d_I \to 0} R_0(d_I) = \max_{j\in\Omega} \frac{\beta_j}{\gamma_j}, \qquad \lim_{d_I\to\infty} R_0(d_I) = \frac{\sum_{j\in\Omega}\alpha_j\beta_j}{\sum_{j\in\Omega}\alpha_j\gamma_j}.$$

For symmetric $L$ the second limit is $\sum_j \beta_j / \sum_j \gamma_j$. In particular, faster movement of infected individuals lowers the reproduction number from the worst patch ratio to the $\alpha$-weighted average.

## Depends on

- [SIS patch model and its basic reproduction number](sis-patch-model-and-its-basic-reproduction-number.md)

## Expansion

The key input is a spectral-bound monotonicity lemma (Lemma 2.5, related to Karlin's reduction principle): for irreducible quasi-positive $L$ and real $f_j$ not all equal, $s(d_I L + \operatorname{diag}(f_j))$ is strictly decreasing in $d_I$, tends to $\max_j f_j$ as $d_I \to 0$, and tends to $\sum_j f_j\alpha_j$ as $d_I \to \infty$. Writing $R_0$ through the sign relation $R_0 = 1/\mu$ where $\mu$ solves $s\big(d_I L + \operatorname{diag}(\mu\beta_j - \gamma_j)\big) = 0$, monotonicity of the spectral bound in $d_I$ and in $\mu$ transfers to $R_0$. This is Theorem 2.6 (with the bounds (2.3) proved within it), Theorem 2.7 and Remark 2.8. Earlier proofs required all $\beta_j, \gamma_j > 0$.

## Sources

- S. Chen, J. Shi, Z. Shuai, Y. Wu, "Asymptotic profiles of the steady states for an SIS epidemic patch model with asymmetric connectivity matrix", Journal of Mathematical Biology 80 (2020), 2327–2361, <https://doi.org/10.1007/s00285-020-01497-8>.
