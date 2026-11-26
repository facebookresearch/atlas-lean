# Stationary law and Poincaré inequality for the Wright–Fisher diffusion with immigration

Consider the two-species Wright–Fisher diffusion with constant selection $s$, immigration rate $m\ge0$ and metacommunity proportion $p\in(0,1)$,

$$ dX_t=\big[m(p-X_t)+sX_t(1-X_t)\big]dt+\sqrt{2X_t(1-X_t)}\,dB_t,\qquad X_t\in[0,1], $$

with generator $\mathscr Lf=x(1-x)f''+[m(p-x)+sx(1-x)]f'$.

- Without immigration ($m=0$) the boundaries are absorbing and reached in finite time almost surely, also when $s_t$ switches randomly between $\pm s_0$ on intervals of fixed length; for constant $s\neq0$ the fixation probability is $P_x(T_1<T_0)=(e^{-sx}-1)/(e^{-s}-1)$.
- With immigration, the boundary $1$ is accessible if and only if $m(1-p)<1$, and $0$ is accessible if and only if $mp<1$; otherwise the boundary is not reached. The process has the unique invariant probability density

$$ \pi(x)=c\,x^{mp-1}(1-x)^{m(1-p)-1}e^{sx},\qquad 0<x<1. $$

- For $s>0$, $\pi$ satisfies the Poincaré inequality $\mathrm{Var}_\pi(f)\le C_P\int_0^1 f'(x)^2\,x(1-x)\,\pi(x)\,dx$ with

$$ C_P\le\min\Big\{\frac{e^s}{m},\ \frac{8e^{(1-M)s}}{m}\Big\}, $$

where $M$ is a median of $\pi$. Hence the law of $X_t$ converges to $\pi$ exponentially fast in $L^2(\pi)$, $\mathrm{Var}_\pi(P_tf)\le e^{-2t/C_P}\mathrm{Var}_\pi(f)$.

For the stationary Simpson index this gives $E_\pi[\mathscr S]=1-2E_\pi[X]+2E_\pi[X^2]$, computable from moments of the Beta-type density $\pi$; when $s=0$, $\pi$ is the $\mathrm{Beta}(mp,m(1-p))$ law.

## Expansion

The density solves the stationary Fokker–Planck equation, $\pi\propto\frac{1}{x(1-x)}\exp\int\frac{m(p-x)+sx(1-x)}{x(1-x)}\,dx$. Feller's boundary classification for the scale function $x^{-mp}(1-x)^{-m(1-p)}e^{-sx}$ gives the accessibility criteria. For $s=0$ the generator is a Jacobi operator with spectral gap $m$, so $C_P=1/m$; the tilt $e^{sx}$ has oscillation $s$ on $[0,1]$, so the Holley–Stroock perturbation lemma gives $C_P\le e^s/m$, and a Hardy-type criterion around a median gives the second bound.

## Sources

- A. Personne, A. Guillin and F. Jabot, "On the Simpson index for the Moran process with random selection and immigration", arXiv:1809.08890 (2018), <https://doi.org/10.48550/arXiv.1809.08890>. Proposition 12 (absorption and fixation without immigration), Proposition 14 (random switching selection), Proposition 15 (boundary accessibility), the invariant density in the subsection on the case with immigration, and Proposition 16 (Poincaré inequality). The value of $C_P$ for $s=0$ and the exponential decay rate are the standard consequences used in its proof. Published version: International Journal of Biomathematics 13 (2020) 2050046, <https://doi.org/10.1142/s1793524520500461>.
