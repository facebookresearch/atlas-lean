# Linear chain trick for dwell times given by Poisson-process $k$-th event times with time-varying rate

**Setting.** Let $r(t) \ge 0$ be an integrable rate and $m(t,\tau) = \int_\tau^t r(s)\,ds$. The $k$-th event time of a (possibly nonhomogeneous) Poisson process with rate $r(t)$ started at time $\tau$ has density and survival function

$$ h_r^k(t,\tau) = r(t)\,\frac{m(t,\tau)^{k-1}}{(k-1)!}\,e^{-m(t,\tau)}, \qquad \mathcal S_r^k(t,\tau) = \sum_{j=1}^k u_r^j(t,\tau), \quad u_r^j(t,\tau) = \frac{m(t,\tau)^{j-1}}{(j-1)!}\,e^{-m(t,\tau)}. $$

For constant $r$ this is the Erlang$(r,k)$ law. The functions $u_r^j$ satisfy the chain relations

$$ \frac{\partial}{\partial t}u_r^1(t,\tau) = -r(t)\,u_r^1(t,\tau), \qquad \frac{\partial}{\partial t}u_r^j(t,\tau) = r(t)\big(u_r^{j-1}(t,\tau) - u_r^j(t,\tau)\big), \quad j \ge 2, $$

with $u_r^1(\tau,\tau) = 1$ and $u_r^j(\tau,\tau) = 0$ for $j \ge 2$.

**Theorem (extended linear chain trick).** Particles enter a state X at a non-negative integrable rate $\mathcal I_X(t)$ and stay there for a Poisson-process $k$-th event time with rate $r(t)$ (independently across particles), then move to a state Y, which also receives an inflow $\mathcal I_Y(t)$ and whose dwell time has survival function $S_Y(t,\tau)$. With $x(0) = x_0$, $y(0) = y_0$, the mean-field integral equations

$$ x(t) = x_0\,\mathcal S_r^k(t,0) + \int_0^t \mathcal I_X(s)\,\mathcal S_r^k(t,s)\,ds, \qquad y(t) = y_0 S_Y(t,0) + \int_0^t \Big(\mathcal I_Y(\tau) + x_0 h_r^k(\tau,0) + \int_0^\tau \mathcal I_X(s)\,h_r^k(\tau,s)\,ds\Big) S_Y(t,\tau)\,d\tau $$

are equivalent to $x = \sum_{j=1}^k x_j$ with

$$ \dot x_1 = \mathcal I_X(t) - r(t)\,x_1, \qquad \dot x_j = r(t)\,(x_{j-1} - x_j), \quad j = 2,\dots,k, \qquad x_1(0) = x_0,\ x_j(0) = 0 \ (j \ge 2), $$

and $y(t) = y_0 S_Y(t,0) + \int_0^t \big(\mathcal I_Y(\tau) + r(\tau)\,x_k(\tau)\big) S_Y(t,\tau)\,d\tau$. Explicitly, $x_j(t) = x_0\,u_r^j(t,0) + \int_0^t \mathcal I_X(s)\,u_r^j(t,s)\,ds$ is the expected amount that has experienced exactly $j-1$ of the $k$ events. If Y is left at per-capita rate $\mu(t)$, the last equation becomes $\dot y = \mathcal I_Y(t) + r(t)\,x_k - \mu(t)\,y$.

## Expansion

The chain relations follow by differentiating $m^{j-1}e^{-m}/(j-1)!$ using $\partial_t m(t,\tau) = r(t)$. Writing $\mathcal S_r^k$ as the sum of the $u_r^j$ splits $x$ into the $x_j$; differentiating each $x_j$ under the integral (Leibniz rule) and applying the chain relations gives the ODEs, and the outflow density $h_r^k = r\,u_r^k$ shows that the flux into Y is $r(t)\,x_k(t)$. The classical Erlang linear chain trick is the case of constant $r$. Because only the rate is time-dependent, it may also be made state-dependent (for example a treatment rate that tracks the epidemic) while keeping a finite ODE system. The weak memorylessness of first event times (the remaining time to the first event, given none by time $s$, is again a first event time started at $s$) is what makes each sub-state exponential-like with rate $r(t)$.

## Sources

- Paul J. Hurtado and Adam S. Kirosingh, "Generalizations of the 'Linear Chain Trick': Incorporating more flexible dwell time distributions into mean field ODE models", arXiv:1808.07571 (2018): Section 3, Lemma 2 and Theorem 3 (extended LCT for Poisson process $k$-th event times), with Definition 1 (weak memorylessness) and Corollary 1. <https://doi.org/10.48550/arXiv.1808.07571> Published version: Journal of Mathematical Biology. 79, 1831-1883, October 2019, <https://doi.org/10.1007/s00285-019-01412-w>.
