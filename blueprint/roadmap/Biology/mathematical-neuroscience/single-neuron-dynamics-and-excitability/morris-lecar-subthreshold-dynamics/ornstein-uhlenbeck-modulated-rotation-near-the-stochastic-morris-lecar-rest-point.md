# Ornstein–Uhlenbeck modulated rotation near the stochastic Morris–Lecar rest point

Consider the stochastic Morris–Lecar neuron $dV_t=f(V_t,W_t)\,dt$, $dW_t=g(V_t,W_t)\,dt+h(V_t,W_t)\,dB_t$, with noise in the potassium gating variable $W$. Assume the input current is in the regime where the deterministic system has a stable focus $(V_{\rm eq},W_{\rm eq})$ inside an unstable limit cycle. Linearizing around the focus, with the diffusion frozen at the equilibrium, gives

$$
dX_t=MX_t\,dt+G\,dB_t,\qquad X_t=(V_t-V_{\rm eq},\,W_t-W_{\rm eq})^\top,
$$

with $M$ having complex eigenvalues $-\lambda\pm i\omega$ ($\lambda>0$) and $G=\mathrm{diag}(0,\sigma)$. Choose $Q$ with $Q^{-1}MQ=\begin{pmatrix}-\lambda&\omega\\-\omega&-\lambda\end{pmatrix}$, set $B=Q^{-1}GG^\top Q^{-\top}$ and $\tau^2=\tfrac12\operatorname{tr}B=-\frac{\sigma^2m_{12}}{2\omega^2m_{21}}$.

**Stochastic averaging (Baxendale–Greenwood).** With $R_s$ the rotation by angle $s$, the rescaled process $U_t=\frac{\sqrt\lambda}{\tau}R_{\omega t/\lambda}Q^{-1}X_{t/\lambda}$ converges in law on every finite interval $[0,t^*]$, as $\lambda/\omega\to0$, to the standard two-dimensional Ornstein–Uhlenbeck process $dS_t=-S_t\,dt+dB_t$. Hence, in distribution,

$$
X_t\approx\frac{\tau}{\sqrt\lambda}\,Q\,R_{-\omega t}\,S_{\lambda t}:
$$

subthreshold oscillations are a fixed linear image of a uniform rotation at frequency $\omega$, whose amplitude and phase are modulated by a slow 2D OU process.

The radius $|S_t|$ is a radial Ornstein–Uhlenbeck (Bessel-type) diffusion, which is a one-dimensional leaky integrate-and-fire model before firing. Adding a firing rule calibrated on Morris–Lecar firing statistics, with firing as a function of radius, reproduces the Morris–Lecar interspike-interval distribution while keeping the computational cost of an LIF model. In the parameter regime studied, $\lambda$ is one order of magnitude smaller than $\omega$.

## Proof sketch

Conjugating by $Q$ makes the drift a damped rotation. Removing the rotation with $R_{\omega t}$ leaves a pure OU drift $-\lambda$ with a rotating diffusion matrix $R_{\omega t}C$. On the slow time $\lambda t$ the fast rotation averages $R_{\omega t}BR_{\omega t}^\top$ to $\tau^2I$, which by a martingale-problem argument gives an isotropic OU limit. The identity $(m_{11}+\lambda)^2+\omega^2=-m_{12}m_{21}$ gives the closed form of $\tau^2$.

## Related topics

- [Leaky integrate-and-fire neuron](../../leaky-integrate-and-fire-neuron/README.md)

## Sources

- Susanne Ditlevsen and Priscilla Greenwood, "The Morris–Lecar neuron model embeds a leaky integrate-and-fire model", *Journal of Mathematical Biology* 67 (2013), 239–259, <https://doi.org/10.1007/s00285-012-0552-7>. Preprint version: arXiv:1108.0073 (2011), Sections 3–4 (linear system (linearsystem), Eqs. (tau2), (dUt), the averaging theorem, Eq. (Xapprox)) and Sections 5–6, <https://doi.org/10.48550/arXiv.1108.0073>.
