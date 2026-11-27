# Noise-induced stabilization of homogeneous states in a ring neural field

**Setting.** Consider the Gaussian moment equations of a one-layer stochastic firing-rate neural field on the ring $\Gamma=\mathbb{S}^1=[0,1)$ with $\lambda(dr)=dr$, constant time constant $\theta$, constant additive noise $\Lambda$, translation-invariant weights $J(r-r')$, weight-noise $\sigma(r-r')$ and delays $\tau(r-r')$, and sigmoid $S(x)=\Phi(gx)$ with $g>0$, $\Phi$ the standard Gaussian distribution function, so that $f(\mu,v)=\Phi\big(g\mu/\sqrt{1+g^2v}\big)$. Set $\mathcal{J}=\int_0^1 J$, $\tilde\sigma=\int_0^1\sigma$ (so that the weight-noise term of the variance equation at a homogeneous state is $\tilde\sigma^2F_0^2$), $F_0=f(0,v)$ (independent of $v$) and choose the input $I=-\mathcal{J}F_0$. Then

$$
(\mu_0,v_0)=\Big(0,\ \tfrac{\theta}{2}\big(\tilde\sigma^2F_0^2+\Lambda^2\big)\Big)
$$

is a spatially homogeneous equilibrium.

**Proposition (Touboul 2011, Section 3.1).** Let $a_k(\nu)=\int_{\Gamma}J(r)e^{-\nu\tau(r)}e^{-2\pi i k r}\,dr$, $k\in\mathbb{Z}$. The linearization at $(\mu_0,v_0)$ is block-triangular; its characteristic roots are $-2/\theta$ together with the solutions $\nu$ of the dispersion relations

$$
\nu=-\frac1\theta+\frac{g}{\sqrt{2\pi(1+g^2v_0)}}\,a_k(\nu),\qquad k\in\mathbb{Z}.
$$

In particular no instability can originate in the variance equation. With $a_M$ the Fourier coefficient of largest real part, the homogeneous state is linearly stable whenever

$$
\operatorname{Re}\Big(-\frac1\theta+a_M\,\frac{g}{\sqrt{2\pi(1+g^2v_0)}}\Big)<0 .
$$

Hence: if $-1/\theta+\operatorname{Re}(a_M)\,g/\sqrt{2\pi}<0$ the state is stable for every noise level; otherwise it is unstable for small $\Lambda,\sigma$ and becomes stable once $v_0$ (which increases with $\Lambda^2$ and $\tilde\sigma^2$) is large enough, since the leading root tends to $-1/\theta$ as $v_0\to\infty$.

**Non-delayed homogeneous system.** Without delays, for large gain $g$ the homogeneous equilibrium undergoes a pitchfork bifurcation as the noise is decreased, along the curve

$$
\tilde\sigma^2F_0^2+\Lambda^2=\Big(\frac{\mathcal{J}^2\theta^2g^2}{2\pi}-1\Big)\frac{2}{\theta g^2},
$$

below which $(\mu_0,v_0)$ is unstable and two further homogeneous equilibria exist. With purely synaptic delays $\tau\equiv\tau_d$ and exponential weights $J(r)=e^{-|r|/s}$, Turing–Hopf roots $\nu=i\omega_k$ exist only when $v_0=\frac{\theta}{2}\big(\tilde\sigma^2F_0^2+\Lambda^2\big)\le \frac{\theta^2}{2\pi}\frac{(1-e^{-1/s})^2}{1/s^2+4\pi^2k^2}-\frac{1}{g^2}$; so sufficiently strong noise suppresses delay-induced oscillatory instabilities.

## Depends on

- [Gaussian moment equations of the stochastic firing-rate neural field](gaussian-moment-equations-of-the-stochastic-firing-rate-neural-field.md)

## Proof sketch

At $\mu_0=0$ the derivative $\partial_v f$ vanishes, so perturbations of the variance do not feed back into the mean, while $\partial_\mu f=g/\sqrt{2\pi(1+g^2v_0)}=:F_0'$. The convolution structure on the ring diagonalizes the mean equation on Fourier modes $e^{\nu t+2\pi i k r}$, giving the scalar dispersion relation for each $k$. For $\nu=i\omega$ the dispersion relation gives $\omega^2+1/\theta^2=F_0'^2|a_k(i\omega)|^2$ with $F_0'^2=g^2/(2\pi(1+g^2v_0))$, so a root on the imaginary axis needs $F_0'|a_k|\ge1/\theta$, a condition on $v_0$ (the source's Section 3.1 writes it on $\tilde\sigma^2F_0^2+\Lambda^2$ instead of $v_0$). Noise enters only through $v_0$, which divides the effective gain $F_0'$: larger noise lowers the slope of the averaged sigmoid and pushes every mode toward the leak rate $-1/\theta$.

## Sources

- Jonathan Touboul, "Mean-field equations for stochastic firing-rate neural fields with delays: Derivation and noise-induced transitions", *Physica D: Nonlinear Phenomena* 241 (2012), 1223–1244, <https://doi.org/10.1016/j.physd.2012.03.010>. Preprint version: arXiv:1108.2407 (2011), <https://doi.org/10.48550/arXiv.1108.2407>.
