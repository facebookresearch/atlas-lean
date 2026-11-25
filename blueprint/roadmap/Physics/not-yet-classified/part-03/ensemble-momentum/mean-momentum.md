# Exact ensemble-averaged momentum equation

Let $\mu$ be a probability measure on the realizations $\omega$, $\rho$ a constant density, $(t, x)$ a point in $\mathbb{R} \times \mathbb{R}^{n+1}$ and $\varepsilon > 0$. Write the momentum flux of component $j$ as $\Phi_j(\rho, v, \sigma)_i = \rho v_j v_i - \sigma_{ji}$. Suppose:

- every velocity component $u_i(\tau, y)$ is square-integrable in $\omega$, and every stress component $\sigma_{ji}(t, y)$ is integrable;
- almost surely, $u_j(\cdot, x)$ is differentiable at every point of the ball of radius $\varepsilon$ about $t$, and $u_i(t, \cdot)$ and $\sigma_{ji}(t, \cdot)$ are differentiable at every point of the ball of radius $\varepsilon$ about $x$;
- the time derivative of $u_j$ and the spatial derivatives of $u_i$ and $\sigma_{ji}$ at the point are a.e. strongly measurable in $\omega$;
- one integrable $B$ almost surely bounds the time derivatives of $u_j$ on the time ball and the spatial derivatives of $u_i$, of $u_j u_i$ and of $\sigma_{ji}$ on the space ball;
- almost surely, $\partial_t(\rho u_j) + \operatorname{div} \Phi_j(\rho, u, \sigma) = f_j$ at $(t, x)$ for every $j$.

Then for each $j$, at $(t, x)$,

$$\partial_t(\rho\, \mathbb{E}[u_j]) + \operatorname{div} \Phi_j(\rho, \mathbb{E}[u], \mathbb{E}[\sigma]) = \mathbb{E}[f_j] - \rho \operatorname{div}_i \operatorname{Cov}(u_j, u_i),$$

where $\operatorname{Cov}(u_j, u_i) = \mathbb{E}[u'_j u'_i]$ is the Reynolds stress per unit density. No integrability of the body force $f$ is assumed.
