# Gaussian moment equations of the stochastic firing-rate neural field

**Model.** Neural populations sit at locations $r$ of a field $\Gamma$ distributed with density $\lambda$. In the mean-field (propagation-of-chaos) limit of a network of noisy Wilson–Cowan firing-rate neurons with delayed interactions, the voltage $\bar V_t(r)$ of a typical neuron at $r$ solves the McKean–Vlasov delay SDE

$$
d\bar V_t(r)=\Big(-\frac{\bar V_t(r)}{\theta(r)}+I(r,t)+\int_\Gamma J(r,r')\,\mathbb{E}\big[S(r',\bar V_{t-\tau(r,r')}(r'))\big]\lambda(r')\,dr'\Big)dt
+\Lambda(r,t)\,dW_t+\int_\Gamma \sigma(r,r')\,\mathbb{E}\big[S(r',\bar V_{t-\tau(r,r')}(r'))\big]\lambda(r')\,dr'\,dB_t ,
$$

where $\theta(r)>0$ is the membrane time constant, $I$ the deterministic input, $\Lambda$ the additive noise intensity, $J$ the synaptic weights, $\sigma$ the intensity of the synaptic-weight noise, $\tau(r,r')\ge 0$ the propagation delays, $S(r,\cdot)$ a bounded, uniformly Lipschitz sigmoid, and $W,B$ independent standard Brownian motions.

**Theorem (Touboul 2011, Theorem 3).** If the initial condition $(V^0_t(r))_{t\in[-\tau,0]}$ is a Gaussian chaotic process, the solution of the mean-field equation is Gaussian for all $t\ge 0$. Writing $\mu(r,t)$ for its mean and $v(r,t)$ for its variance, $\mathbb{E}[S(r,V_t(r))]=f(r,\mu(r,t),v(r,t))$ with

$$
f(r,\mu,v)=\int_{\mathbb{R}} S\big(r,\,x\sqrt{v}+\mu\big)\,\frac{e^{-x^2/2}}{\sqrt{2\pi}}\,dx ,
$$

and $(\mu,v)$ solve the closed system of delayed integro-differential equations

$$
\begin{aligned}
\partial_t\mu(r,t)&=-\frac{\mu(r,t)}{\theta(r)}+\int_\Gamma J(r,r')\,f\big(r',\mu(r',t-\tau(r,r')),v(r',t-\tau(r,r'))\big)\lambda(r')\,dr'+I(r,t),\\
\partial_t v(r,t)&=-\frac{2\,v(r,t)}{\theta(r)}+\Big(\int_\Gamma \sigma(r,r')\,f\big(r',\mu(r',t-\tau(r,r')),v(r',t-\tau(r,r'))\big)\lambda(r')\,dr'\Big)^2+\Lambda(r,t)^2,
\end{aligned}
$$

with initial data given by the mean and variance of $V^0$ on $[-\tau,0]$. For a finite number $P$ of populations the integrals become sums $\sum_{\beta=1}^P J_{\alpha\beta}f_\beta(\cdot)$ and $\big(\sum_{\beta}\sigma_{\alpha\beta} f_\beta(\cdot)\big)^2$ (a system of $2P$ delay differential equations). The weight noise enters through the single Brownian motion $B$, so its contribution to the variance is the square of its total coefficient; the source's equation (8) prints $\int_\Gamma\sigma^2f^2\lambda^2$, the variance of a noise that is independent across source locations $r'$, which does not match the equation above (for $\Gamma=[0,1]$, $\lambda\equiv1$, $\sigma(r,r')=2r'$, $J=I=\Lambda=\tau=0$, $\theta=1$, $S=\Phi$ and $V^0\equiv0$, $d\bar V=-\bar V\,dt+\tfrac12dB_t$ has $v(t)=(1-e^{-2t})/8$, while that formula gives $(1-e^{-2t})/6$). Under non-degeneracy conditions this moment system has a unique solution (Theorem 4).

**Gaussian-distribution sigmoid.** For $S(r,x)=\Phi(g(r)x+h(r))$, where $\Phi(x)=\int_{-\infty}^x e^{-u^2/2}\,du/\sqrt{2\pi}$ is the standard Gaussian distribution function (the convention the paper calls erf),

$$
f(r,\mu,v)=\Phi\!\Big(\frac{g(r)\mu+h(r)}{\sqrt{1+g(r)^2 v}}\Big),
$$

so the noise level enters the mean equation by flattening the effective gain. In the zero-noise limit ($\Lambda\equiv0$, $\sigma\equiv 0$, $v(\cdot,0)=0$) the mean equation reduces to the classical delayed Wilson–Cowan neural field.

## Proof sketch

The drift is linear in $\bar V$ and the interaction terms depend only on the law of the solution, so the variation-of-constants formula writes $\bar V_t(r)$ as $e^{-t/\theta(r)}V^0_0(r)$ plus a deterministic integral plus Wiener integrals of deterministic integrands against $W$ and $B$; such a process is Gaussian. Taking the mean and the variance of this representation (Itô isometry for the two independent stochastic integrals, whose integrands are $\Lambda$ and $\int_\Gamma\sigma f\lambda\,dr'$) gives the two equations. Covariances between distinct locations vanish, so $(\mu,v)$ characterize the whole law. The point of the reduction is that noise becomes a parameter of a deterministic delay system, so standard bifurcation theory applies to the stochastic field.

## Sources

- Jonathan Touboul, "Mean-field equations for stochastic firing-rate neural fields with delays: Derivation and noise-induced transitions", *Physica D: Nonlinear Phenomena* 241 (2012), 1223–1244, <https://doi.org/10.1016/j.physd.2012.03.010>. Preprint version: arXiv:1108.2407 (2011), <https://doi.org/10.48550/arXiv.1108.2407>.
