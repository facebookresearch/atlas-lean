# Entrywise explicit formula for xi-derivative windows

For fixed $0<\lambda<1$ and a nondecreasing $C^3$ taper $\varrho$, zero on $(-\infty,0]$ and one on $[1,\infty)$, put $\ell_T=\log(T/(2\pi))$, $L_T=\lambda\ell_T$, and $X_T=e^{L_T}$. Use fixed ramp width $w=1$, grid $\tau_k=T+2\pi k/L_T$ for $0\le k<\lfloor L_T T/(2\pi)\rfloor$, and envelope $\phi_{T,v}(u)=\sqrt{\max(0,v(u/L_T))}\,\varrho((L_T/2-|u|)/w)$. The two profiles here are $v=1$ and

$$
v(s)=1-\tfrac7{100}(2s)^2-\tfrac{51}{200}(2s)^4.
$$

With the positive-sign Fourier transform $\widehat\phi_{T,v}(z)=\int\phi_{T,v}(u)e^{izu}\,du$, set $H_k(z)=\widehat\phi_{T,v}(z-\tau_k)$. For all sufficiently large $T$ and all grid indices $k,l$, the sum $(G_1)_{kl}=\sum_\rho m_\rho H_k(\gamma_\rho)H_l(\gamma_\rho)$ is absolutely convergent over the zeros of $\xi'$, where $\gamma_\rho=(\rho-1/2)/i$. Let $M_{kl}$ be the real-line integral of $H_k(t)H_l(t)$ against the density $\mu(t)+\Pi_{X_T}(t)+P_{c_{kl}}(X_T;t)$, with

$$
\begin{aligned}
\mu(t)&=\big(\operatorname{Re}\psi(1/4+it/2)-\log\pi\big)/(2\pi),\\
\Pi_X(t)&=\frac{1}{2\pi(1/4+t^2)}+\frac1\pi\operatorname{Re}\frac{X^{1/2+it}-1}{1/2+it},\\
P_c(X;t)&=\frac1\pi\operatorname{Re}\sum_{1\le n\le X} c(n)n^{-1/2-it}.
\end{aligned}
$$

Here $\psi=\Gamma'/\Gamma$ and $c_{kl}(n)=C(n;\tfrac12\log(\tau_{kl}/(2\pi))+i\pi/4)$ with $\tau_{kl}=(\tau_k+\tau_l)/2$. For the prime polynomial use the coefficients

$$
C(n;B)=-\Lambda(n)+\sum_{0\le j<\Omega(n)}B^{-j-1}[(\Lambda\cdot\log)*\Lambda^{*j}](n),
$$

where $\Omega(n)$ counts prime factors with multiplicity and $*$ is Dirichlet convolution. There exist $C_0,\eta$ with $\eta>0$ such that eventually, uniformly over $k,l$ at each height,

$$
|(G_1)_{kl}-M_{kl}|\le C_0T^{-\eta}\left(\frac1{\max(1,|\tau_k-\tau_l|^2)}+\frac1T\right).
$$

## Depends on

- [Riemann xi function](riemann-xi.md)

## Proof depends on

- [Zeros of the xi derivative lie in the open critical strip](zeros-of-the-xi-derivative-in-the-open-critical-strip.md)
- [Dyadic and local counts for the xi derivative](xi-derivative-riemann-von-mangoldt.md)

## Expansion

Move the weighted contour for the logarithmic derivative of $\xi'$ to the fixed line with real part $5/4$. Prove summability from the derivative local count and the window's decay; identify the pole term with weight one and the entry-dependent prime polynomial. Keep the on-diagonal value of the separation factor equal to one and keep the $1/T$ floor in the error. Justify the packet hypotheses separately for the flat and quartic envelopes.

## Sources

- [Window profiles and realization](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Defs.lean#L190-L207)
- [Prime-side density and the entry-dependent base point](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Defs.lean#L96-L146)
- [Derivative explicit formula and precise error](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Statement.lean#L191-L208)
- [Unconditional flat and profile instances](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Final.lean#L93-L98)
- [Profile instance](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Final.lean#L352-L363)
