# Finite-time blow-up of excitatory noisy integrate-and-fire networks

**Model.** The nonlinear noisy leaky integrate-and-fire (NNLIF) population model describes the density $p(v,t) \ge 0$ of neurons at membrane potential $v \in (-\infty, V_F]$, with firing threshold $V_F$ and reset potential $V_R < V_F$:

$$\partial_t p + \partial_v\big[h(v, N(t))\,p\big] - a(N(t))\,\partial_v^2 p = \delta(v - V_R)\,N(t), \qquad v < V_F,$$

$$p(V_F, t) = 0, \qquad p(-\infty, t) = 0, \qquad p(v, 0) = p^0(v), \qquad \int_{-\infty}^{V_F} p^0 = 1,$$

where the mean firing rate is the outgoing flux at threshold,

$$N(t) = -a(N(t))\,\partial_v p(V_F, t) \ge 0.$$

The standard coefficients are $h(v,N) = -v + bN$ and $a(N) = a_0 + a_1 N$ with $a_0 > 0$, $a_1 \ge 0$; the connectivity $b$ is positive for average-excitatory and negative for average-inhibitory networks. A weak solution is a pair $(p, N)$ with $p \in L^\infty(\mathbb{R}_+; L^1_+(-\infty, V_F))$ and $N \in L^1_{\mathrm{loc},+}(\mathbb{R}_+)$ satisfying the equation against smooth test functions.

**Theorem.** Assume $h(v,N) + v \ge bN$ and $a(N) \ge a_m > 0$ for all $v \le V_F$ and $N \ge 0$, with $b > 0$. Let $\mu > \max(V_F/a_m, 1/b)$. If

$$\int_{-\infty}^{V_F} e^{\mu v}\,p^0(v)\,dv$$

is large enough, that is, if the initial data are concentrated enough near the threshold $V_F$, then the problem has no global-in-time weak solution.

## Proof sketch

The proof tests the weak formulation with $\phi(v) = e^{\mu v}$ and follows $M_\mu(t) = \int e^{\mu v}p(v,t)\,dv$. Since $p(\cdot,t)$ is a probability density on $(-\infty, V_F]$, $M_\mu(t) \le e^{\mu V_F}$ for all $t$. The drift bound $h(v,N) \ge bN - v$ and the diffusion bound $a \ge a_m$ make the firing-rate contributions to $\frac{d}{dt}M_\mu$ nonnegative once $\mu > \max(V_F/a_m, 1/b)$, and yield a differential inequality forcing $M_\mu$ to grow. If $M_\mu(0)$ is close enough to its upper bound, this growth would push $M_\mu$ above $e^{\mu V_F}$ in finite time, which is impossible; hence no weak solution exists globally, and the firing rate $N$ cannot remain locally integrable. Excitation feeds back on itself through $N$: more firing shifts the population toward threshold, which increases firing.

## Sources

- María J. Cáceres, José A. Carrillo and Benoît Perthame, "Analysis of Nonlinear Noisy Integrate&Fire Neuron Models: blow-up and steady states", *The Journal of Mathematical Neuroscience* 1 (2011), 7, <https://doi.org/10.1186/2190-8567-1-7>. Preprint version: arXiv:1010.4683 (2010), model and coefficient assumptions (Section 1), Definition 2.1 and Theorem 2.2 (Section 2), <https://doi.org/10.48550/arXiv.1010.4683>.
