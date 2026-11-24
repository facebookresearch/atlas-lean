# Unique optimal liquidation path with quadratic costs

Let $N \ge 1$, $\Delta > 0$, $\eta > 0$, $\kappa = \lambda\sigma^2 \ge 0$ and $X_0 \in \mathbb{R}$. Among inventory paths $x_0, \dots, x_N$ with $x_0 = X_0$ and $x_N = 0$, the cost $\sum_{k<N}\Delta[\eta((x_{k+1} - x_k)/\Delta)^2 + \kappa x_k^2]$ has exactly one minimizer. For $N \ge 2$ its interior values solve the second-order difference equations $\eta(x_{k+1} - 2x_k + x_{k-1})/\Delta^2 = \kappa x_k$ for $1 \le k \le N - 1$; for $N = 1$ there are no interior values and the unique path is $(X_0, 0)$. Proof: the cost is a quadratic in the interior vector whose quadratic part is positive definite (the first-difference term alone is, with fixed endpoints), so it has a unique minimizer, characterized by vanishing partial derivatives.

## Sources

- R. Almgren and N. Chriss, "Optimal execution of portfolio transactions", *Journal of Risk* 3(2):5–39, 2000, §2, equations (16)–(17), <https://www.smallake.kr/wp-content/uploads/2016/03/optliq.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
