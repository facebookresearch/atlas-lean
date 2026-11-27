# Explicit growth rate and exponentially small inflation threshold of the periodic two-patch model

**Model (periodic $(1)$-model).** Densities $x_1,x_2>0$ in two patches with symmetric dispersal rate $m\ge0$ obey

$$\dot x_1=(u(t)-\varepsilon)x_1+m(x_2-x_1),\qquad \dot x_2=(-u(t)-\varepsilon)x_2+m(x_1-x_2),$$

with $0\le\varepsilon\le1$ and $u$ of period $2T$, equal to $+1$ on $[0,T)$ and $-1$ on $[T,2T)$. Each patch alternates between growth rate $1-\varepsilon>0$ and $-(1+\varepsilon)<0$, out of phase with the other, so each patch alone is a sink (mean rate $-\varepsilon$). For $m>0$ both patches share a growth rate $\Delta(\varepsilon,m,T)=\lim_t\frac1t\ln x_i(t)$; *inflation* means $\Delta>0$.

**Statements.**
1. *(Closed form.)* With $b=e^{T\sqrt{1+m^2}}$ and $C=m^2b^4+2m^2b^2+4b^2+m^2$,

$$\Delta(\varepsilon,m,T)=\frac{1}{2T}\ln\frac{m^2b^4+2b^2+m^2+m(b^2-1)\sqrt C}{2(1+m^2)b^2}-(m+\varepsilon).$$

2. *(Limits.)* $\lim_{T\to\infty}\Delta=\sqrt{1+m^2}-(m+\varepsilon)$ and $\lim_{T\to0}\Delta=-\varepsilon$; for fixed $T$, $\Delta\to-\varepsilon$ as $m\to0$ or $m\to\infty$, so inflation can only occur at intermediate dispersal.
3. *(Threshold in the period.)* For $m<\frac{1-\varepsilon^2}{2\varepsilon}$ there is $T^*(\varepsilon,m)$ with no inflation for $T<T^*$ and inflation for $T>T^*$, and $\inf_mT^*(\varepsilon,m)>0$: very fast switching never produces inflation.
4. *(Exponentially small dispersal threshold.)* As $T\to\infty$, the smallest dispersal rate at which $m\mapsto\Delta(\varepsilon,m,T)$ becomes positive satisfies $m^*(\varepsilon,T)\sim e^{-(1-\varepsilon)T}$.
5. *(Robustness.)* If the switching times are i.i.d. with law $\mu$ (in particular for exponential times, a piecewise deterministic Markov process), the growth rate exists almost surely, is given by an ergodic average over the stationary laws of an auxiliary angle process, and tends to $\sqrt{1+m^2}-m-\varepsilon$ when the mean switching time tends to infinity; hence inflation persists whenever $m<\frac{1-\varepsilon^2}{2\varepsilon}$ and switching is slow enough. If at each switch the good patch is chosen at random with probabilities $p_1,p_2$, inflation is possible exactly when $\chi=p_1(1-p_2)+p_2(1-p_1)+p_1+p_2-1-\varepsilon>0$.

## Expansion

In the variables $U=\tfrac12\ln(x_1x_2)$ and $V=\tfrac12\ln(x_1/x_2)$, the system becomes $\dot U=m\cosh(2V)-m-\varepsilon$, $\dot V=u(t)-m\sinh(2V)$, so $V$ is autonomous within each half-period and the growth rate is the time average of $m\cosh(2V)-m-\varepsilon$ along the periodic orbit of $V$; integrating the Riccati-type flow explicitly over a half period gives the logarithmic formula. For long periods, $V$ settles near $\pm\tfrac12\sinh^{-1}(1/m)$, where the population sits mostly in the good patch, and the time average approaches the dominant eigenvalue $\sqrt{1+m^2}-m$ of the frozen system minus $\varepsilon$. The threshold $m^*\sim e^{-(1-\varepsilon)T}$ reflects that a seed population transferred to the new good patch at rate $m$ must regrow by the factor $e^{(1-\varepsilon)T}$ during one half-period to compensate the losses.

## Sources

- Michel Benaïm, Claude Lobry, Tewfik Sari and Edouard Strickler, "Untangling the role of temporal and spatial variations in persistence of populations", Theoretical Population Biology 154 (2023), 1–26, <https://doi.org/10.1016/j.tpb.2023.07.003>; numbering as in arXiv:2111.12633: Section 2 (periodic $(1)$-model, Propositions 2.4-2.8 on $\Delta(\varepsilon,m,T)$, Propositions 2.10-2.14 on random switching and random choice), with the general dispersal-induced growth criterion recalled as Theorem 2.2 from Katriel (2022).
