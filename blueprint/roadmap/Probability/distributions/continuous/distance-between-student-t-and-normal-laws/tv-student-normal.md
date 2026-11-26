# Total variation distance between $t_r$ and $\mathcal{N}(0,1)$

Let $r \in \mathbb{R}$, let $f_r(x) = \frac{\Gamma((r+1)/2)}{\sqrt{r\pi}\,\Gamma(r/2)} (1 + x^2/r)^{-(r+1)/2}$, and let $\varphi(x) = e^{-x^2/2}/\sqrt{2\pi}$ be the standard normal density. Define

$$d(r) = \frac12 \int_{\mathbb{R}} \lvert f_r(x) - \varphi(x) \rvert \, dx,$$

read as $0$ when the integrand is not Lebesgue integrable. For $r > 0$, $f_r$ is the density of Student's $t_r$ distribution and $d(r) = d_{\mathrm{TV}}(t_r, Z)$ is the total variation distance between $t_r$ and $Z \sim \mathcal{N}(0, 1)$. For $r \le 0$ there is no Student law: at $r = 0$ the formula gives $f_0 = 0$, since $\sqrt{0} = 0$ and division by zero is read as $0$, and then $d(0) = 1/2$.
