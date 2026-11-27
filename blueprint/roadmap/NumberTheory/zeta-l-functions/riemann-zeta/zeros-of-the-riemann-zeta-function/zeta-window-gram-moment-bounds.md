# Normalized zeta window trace and Frobenius estimates

For the Riemann zeta function let $N=N(T,2T)$ count open-strip zeros with multiplicity. Fix $0<\lambda<1$, a width $w\ge1$, and a nondecreasing $C^3$ taper $\varrho$ that is zero on $(-\infty,0]$ and one on $[1,\infty)$. For large $T$, put $\ell_T=\log(T/(2\pi))$, $L_T=\lambda\ell_T$, and $d_T=\lfloor L_T T/(2\pi)\rfloor$. The indices are $0\le k,l<d_T$, with $\tau_k=T+2\pi k/L_T$. The flat packet has envelope $\phi_T(u)=\varrho((L_T/2-|u|)/w)$; the Montgomery–Taylor packet multiplies this envelope by $\sqrt{\cos(\sqrt{2}\lambda u/L_T)}$ on its support and is zero off that support. In each case use the actual envelope to form $f_k(u)=\phi_T(u)e^{-i\tau_k u}$ and $a_T=L_T^{-1}\int_{\mathbb R}\phi_T(u)^2\,du$.

Writing $h_f(z)=\int_{\mathbb R} f(u)e^{izu}\,du$ and $\gamma_\rho=(\rho-1/2)/i$, form the raw matrix with entries

$$
(G_z)_{kl}=\sum_\rho m_\rho h_{f_k}(\gamma_\rho)\overline{h_{f_l}(\overline{\gamma_\rho})}.
$$

The sum runs over the full strip zero configuration, with both signs of the ordinate and analytic multiplicities. The trace and squared Frobenius estimate use **hat units** $\widehat G=G_z/(a_T L_T^2)$. The separate tilde matrix is $\widetilde G=G_z/L_T$; only when starting from that matrix does the factor $1/(a_T L_T)$ give hat units. For every $\delta>0$, eventually in $T$,

$$
(1-\delta)N\le\operatorname{Re}\operatorname{tr}\widehat G,\qquad \|\widehat G\|_F^2\le(\kappa(\lambda)+\delta)N.
$$

For the flat envelope, $\kappa(\lambda)=1/\lambda+\lambda/3$. For the Montgomery–Taylor envelope, $\kappa(\lambda)=1/c_*(\lambda)$, where $c_*(\lambda)=\sqrt{2}\sin\theta/(\cos\theta+\theta\sin\theta)$ and $\theta=\lambda/\sqrt{2}$. These are estimates at fixed $\lambda$; taking $\lambda\to1^-$ is a subsequent step. The corresponding limits are $4/3$ and $1/c_*(1)$.

## Depends on

- [Montgomery–Taylor window constant](montgomery-taylor-window-constant.md)

## Proof depends on

- [Weil explicit formula](weil-explicit-formula-for-zeta.md)
- [Dyadic zero count and local estimate](dyadic-riemann-von-mangoldt-and-local-count.md)
- [Montgomery–Vaughan weighted Hilbert inequality](../../../../Analysis/inequalities/hilbert-s-inequality/montgomery-vaughan-weighted-hilbert-inequality.md)

## Expansion

First record the two tapered families and their normalizers, then prove the entrywise equality using the correlation form of Weil. Separate the prime sums, diagonal/off-diagonal estimates and taper errors, using the weighted Hilbert inequality at logarithmic frequencies to bound the off-diagonal prime sums. Combine with the dyadic zero count and only then pass to the window parameter limit.

## Sources

- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/PrimeSideB/Traces.lean).
- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/ThmD/Traces.lean).
- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/FinalMult.lean#L62-L116).
- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/ThmD/Final.lean).
- [Packet, index range, window mass and transforms](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/Defs.lean#L175-L247).
- [Tilde and hat scales and raw zero-side Gram entries](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/Defs.lean#L279-L305).
- [Optimal cosine profile and coefficient](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/ThmD/Functional.lean#L28-L43); [the window realization](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/ThmD/Window.lean#L37-L39).
- [Application at fixed window parameter](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/ThmD/Mult.lean#L96-L116).
