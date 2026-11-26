# Fixed-window xi-derivative count bounds and strict decimal margins

In the flat and quartic xi-derivative families let $N_1$ count zeros with multiplicity, $S_1$ count simple zeros on the critical line, and $D$ count distinct zeros. All three counts use the same half-open ordinate windows and analytic orders of $\xi'$. For either profile $v$, each fixed $0<\lambda<1$ and each $\epsilon>0$, for all large $T$ both inequalities hold:

$$
\begin{aligned}
(2-\kappa_1(\lambda,v)-\epsilon)N_1(T,2T)&\le S_1(T,2T),\\
(3/2-\kappa_1(\lambda,v)/2-\epsilon)N_1(T,2T)&\le D(T,2T).
\end{aligned}
$$

For each profile some $\lambda\in[1/2,1)$ has both unrounded coefficients strictly above the corresponding decimals: $(0.85838,0.92919)$ for the flat window and $(0.86864,0.93432)$ for the quartic window. No uniform height threshold across all $\lambda$ or $\epsilon$ is asserted.

## Depends on

- [Xi-derivative coefficient moments and Gram transfer](xi-derivative-window-moments-and-transfer.md)

## Proof depends on

- [Zeros of the xi derivative lie in the open critical strip](zeros-of-the-xi-derivative-in-the-open-critical-strip.md)
- [Dyadic and local counts for the xi derivative](xi-derivative-riemann-von-mangoldt.md)
- [Rank–trace estimates for extracting distinct and simple zeros](../zeros-of-the-riemann-zeta-function/zero-window-rank-trace-certificates.md)

## Expansion

Deduce the required bounds on the normalized derivative Gram moments, then use the rank–trace inequalities for simple and distinct zeros separately. Control the derivative zero-side reflection blocks and the tail beyond the enlarged interval from the local count and the Fourier decay; for the quartic profile use its own window estimates. For the margins, bound the tail after nine series coefficients on $[0,1]$, certify the two strict inequalities at $\lambda=1$, and use continuity to obtain one $\lambda<1$ for each profile. This fixes the parameter before applying any eventual estimate.

## Sources

- [Fixed-parameter inequalities and both strict certificates](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Statement.lean#L258-L290)
- [Strict margins by continuity from one](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Certificate.lean#L30-L55)
- [Count assembly and tail control](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/XiPrime/Assembly.lean#L138-L202)
