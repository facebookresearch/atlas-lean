# Rate of change of transmission-line energy

Let $R, L, G, C \in \mathbb{R}$, let $U \subseteq \mathbb{R}^2$ be open, and let $v, i : \mathbb{R}^2 \to \mathbb{R}$ be $C^1$ on $U$ and satisfy the telegrapher equations $\partial_x v = -R\,i - L\,\partial_t i$ and $\partial_x i = -G\,v - C\,\partial_t v$ at every point of $U$. For $\ell > 0$ let $E(s) = \int_0^\ell \big(C v(x,s)^2/2 + L i(x,s)^2/2\big)\,dx$. If $[0, \ell] \times \{t\} \subseteq U$, then $E$ is differentiable at $t$ with

$$E'(t) = v(0,t)\,i(0,t) - v(\ell,t)\,i(\ell,t) - \int_0^\ell \big(R\,i(x,t)^2 + G\,v(x,t)^2\big)\,dx.$$
