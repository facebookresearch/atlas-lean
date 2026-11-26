# Integrated energy balance of a finite transmission line

Let $R, L, G, C \in \mathbb{R}$, let $U \subseteq \mathbb{R}^2$ be open, and let $v, i : \mathbb{R}^2 \to \mathbb{R}$ be $C^1$ on $U$ and satisfy the telegrapher equations $\partial_x v = -R\,i - L\,\partial_t i$ and $\partial_x i = -G\,v - C\,\partial_t v$ at every point of $U$. For $\ell > 0$ let $E(s) = \int_0^\ell \big(C v(x,s)^2/2 + L i(x,s)^2/2\big)\,dx$. If $t_0 \le t_1$ and $[0, \ell] \times [t_0, t_1] \subseteq U$, then

$$E(t_1) - E(t_0) = \int_{t_0}^{t_1} \big(v(0,s)\,i(0,s) - v(\ell,s)\,i(\ell,s)\big)\,ds - \int_{t_0}^{t_1} \int_0^\ell \big(R\,i(x,s)^2 + G\,v(x,s)^2\big)\,dx\,ds.$$
