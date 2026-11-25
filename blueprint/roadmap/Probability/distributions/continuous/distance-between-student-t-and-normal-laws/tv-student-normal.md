# Total variation distance between $t_r$ and $\mathcal{N}(0,1)$

Let $r \in \mathbb{R}$, let $f_r(x) = \frac{\Gamma((r+1)/2)}{\sqrt{r\pi}\,\Gamma(r/2)} (1 + x^2/r)^{-(r+1)/2}$ be the density of Student's $t_r$ distribution (for $r > 0$), and let $\varphi(x) = e^{-x^2/2}/\sqrt{2\pi}$ be the standard normal density. The total variation distance between $t_r$ and $Z \sim \mathcal{N}(0, 1)$ is

$$d_{\mathrm{TV}}(t_r, Z) = \frac12 \int_{\mathbb{R}} \lvert f_r(x) - \varphi(x) \rvert \, dx,$$

read as $0$ when the integrand is not Lebesgue integrable.
