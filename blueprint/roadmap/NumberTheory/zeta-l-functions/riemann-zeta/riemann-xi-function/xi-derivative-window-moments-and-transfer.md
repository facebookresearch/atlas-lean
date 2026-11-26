# Xi-derivative coefficient moments and Gram transfer

Use either xi-derivative window above at fixed $0<\lambda<1$. Define $a_T=L_T^{-1}\int\phi_{T,v}^2$, and for every raw matrix $J$ use $\widehat J=J/(a_T L_T^2)$. Let $M^T$ be the prime-side matrix from the same density and packet but with every coefficient frozen at $c_T(n)=C(n;\ell_T/2+i\pi/4)$, instead of the entry-dependent coefficient. Put $N=N_1(T,2T)$ and define

$$
\begin{aligned}
D_1(s)&=s-4s^2+\sum_{j\ge1}\frac{2\cdot4^j(j-1)!}{(2j)!}\,s^{2j+1},\\
A_v(r)&=\int_{-1/2}^{1/2-r} v(s)v(s+r)\,ds,\\
\kappa_1(\lambda,v)&=\frac{\displaystyle\int_{-1/2}^{1/2}v(s)^2\,ds+2\lambda\int_0^1D_1(\lambda r) A_v(r)\,dr}{\displaystyle\lambda\left(\int_{-1/2}^{1/2}v(s)\,ds\right)^2}.
\end{aligned}
$$

For every $\delta>0$, eventually in $T$ the coefficient moments satisfy

$$
(1-\delta)N\le\operatorname{Re}\operatorname{tr}\widehat M^T\le(1+\delta)N,\qquad \|\widehat M^T\|_F^2\le(\kappa_1(\lambda,v)+\delta)N.
$$

The transfer estimates, with the same convention on $\delta$ and eventuality, are

$$
\big|\operatorname{Re}\operatorname{tr}\widehat G_1-\operatorname{Re}\operatorname{tr}\widehat M^T\big|\le\delta N,\qquad
\|\widehat G_1\|_F^2\le (1+\delta)\|\widehat M^T\|_F^2+\delta N.
$$

## Depends on

- [Xi-derivative window explicit formula](xi-derivative-window-explicit-formula.md)

## Proof depends on

- [Dyadic and local counts for the xi derivative](xi-derivative-riemann-von-mangoldt.md)
- [Xi-derivative prime-coefficient reexpansion](xi-derivative-prime-coefficient-reexpansion.md)

## Expansion

Prove summability of $D_1$ and the prime coefficients' diagonal mean, weighted square estimates and off-diagonal estimates. Use the correlation of the particular squared envelope and the derivative Riemann–von Mangoldt count to obtain the fixed-coefficient moments; the flat and quartic window integrals differ. Control the original entry errors in trace and Frobenius norm and apply the reexpansion with its uniform bounds to estimate the difference from freezing all entries at the same complex base point. Combine rather than treating the varying coefficients as fixed without an error estimate.

## Sources

- [Density series, window functional, and profiles](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Defs.lean#L152-L202)
- [Transfer and coefficient moment interfaces](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Statement.lean#L210-L248)
- [The flat application](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Final.lean#L112-L124)
- [The quartic application](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Final.lean#L376-L390)
