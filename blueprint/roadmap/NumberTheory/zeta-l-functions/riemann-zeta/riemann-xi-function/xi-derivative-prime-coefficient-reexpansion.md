# Reexpansion of the xi-derivative prime coefficients

Write $\ell_T=\log(T/(2\pi))$ and $B_T=\ell_T/2+i\pi/4$. For positive integers $n$ let $\Omega(n)$ count prime factors with multiplicity, let $\Lambda$ be the von Mangoldt function, and let $*$ denote Dirichlet convolution. Put

$$
C(n;B)=-\Lambda(n)+\sum_{0\le j<\Omega(n)} B^{-j-1}[(\Lambda\cdot\log)*\Lambda^{*j}](n).
$$

For all sufficiently large $T$, all $0\le x\le1/2$, and all $n\ge1$, the difference $C(n;B_T+x)-C(n;B_T)$ is an absolutely convergent series $\sum_{r\ge1} e_r(T,n)x^r$. The $e_r(T,1)$ vanish. There are constants $A,\rho_0$ with $\rho_0\ge0$ such that for all sufficiently large $T$, every $r\ge1$ and $2\le y\le e^{\ell_T}$, the following hold with $u=\rho_0/\ell_T$:

$$
\begin{aligned}
\sum_{1\le n\le y}|e_r(T,n)|/\sqrt n&\le A u^r\sqrt y\,\ell_T,\\
\sum_{1\le n\le y}|e_r(T,n)|^2&\le A u^{2r} y\,\ell_T^2,\\
\sum_{1\le n\le y}|e_r(T,n)|^2/n&\le A u^{2r}\ell_T^2(1+\log y).
\end{aligned}
$$

## Expansion

Expand each inverse power with its negative-binomial coefficients, then sum over the finite convolution range. Prove the coefficient majorants uniformly in the degree $r$ and in the summation cutoff. For entry $k,l$ of the Gram matrix the shift is $x=\tfrac12\log(\tau_{kl}/T)$, where $\tau_{kl}=(\tau_k+\tau_l)/2$; thus it lies in $[0,1/2]$. The base point is complex; replacing it by $\ell_T/2$ gives a different coefficient family.

## Sources

- [The coefficients and their complex base point](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Defs.lean#L74-L89)
- [Reexpansion and its three uniform bounds](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Transfer/Inputs.lean#L47-L70)
- [Reexpansion at the xi-derivative base point](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Coeff/Reexpansion.lean#L26-L47)
