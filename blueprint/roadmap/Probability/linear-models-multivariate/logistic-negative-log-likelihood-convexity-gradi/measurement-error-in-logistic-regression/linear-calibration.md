# Linear calibration function

For real numbers $\mu_x$ and $\rho$, the linear calibration function is the affine map $w \mapsto \mu_x + \rho(w - \mu_x)$.

In the classical Gaussian measurement-error model, with independent $X \sim \mathcal N(\mu_x, \sigma_x^2)$ and $U \sim \mathcal N(0, \sigma_u^2)$, positive total variance $\sigma_x^2 + \sigma_u^2 > 0$, $W = X + U$ and the reliability ratio $\rho = \sigma_x^2/(\sigma_x^2 + \sigma_u^2)$, it is the conditional mean $\mathbb{E}[X \mid W = w]$. In other models with $W = X + U$ the conditional mean need not be affine: in the normal discriminant class mixture, with within-class variance $v$ and measurement-error variance $v_u$, it is not affine in $w$ when the class means differ and the within-class reliability ratio $v/(v + v_u)$ is less than $1$.
