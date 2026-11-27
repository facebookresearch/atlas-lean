# Persistence window under a maturation-delay trade-off

**Model.** For a maturation delay $\tau\in\mathbb N_0$, mature population size $N_t\ge0$ evolves by

$$N_{t+1}=\frac{N_t}{1+\alpha+\beta N_t}+m(\tau)\,N_{t-\tau},\qquad m(\tau)=\big(a-be^{-K(\tau+1)}\big)\,\overline p^{\,\tau+1},$$

with $\alpha,\beta,a,b,K>0$, $a>b$, and constant immature survival per cycle $\overline p\in(0,1)$. The first term is Beverton–Holt survival of adults; the fecundity $a-be^{-K(\tau+1)}$ increases with $\tau$ while survival to maturity $\overline p^{\tau+1}$ decreases. Initial values $N_{-\tau},\dots,N_0\ge0$ are not all zero, and $m(\tau)\in(0,1)$.

**Equilibria and global dynamics.**

- If $(1+\alpha)m(\tau)<\alpha$, the extinction equilibrium $N_0^*=0$ is the only nonnegative equilibrium and is globally asymptotically stable.
- If $(1+\alpha)m(\tau)>\alpha$, the unique positive equilibrium

$$N_+^*=\frac{(1+\alpha)m(\tau)-\alpha}{\beta\,(1-m(\tau))}$$

exists and is globally asymptotically stable, and $N_0^*$ is unstable.

**Persistence window.** Let $P=\ln(1/\overline p)$. If

$$\Big(\frac{aP}{b(P+K)}\Big)^{P/K}\frac{aK}{P+K}\le\frac{\alpha}{1+\alpha},$$

then no delay gives a positive equilibrium. If the inequality is reversed, there are $\tau_1<\tau_2$ such that $N_+^*(\tau)>0$ exactly for $\tau\in(\tau_1,\tau_2)$. Where it exists, $N_+^*(\tau)$ increases for $\tau<\widehat\tau$ and decreases for $\tau>\widehat\tau$, with

$$\widehat\tau=\frac1K\ln\frac{b(P+K)}{a\,e^{K}P}.$$

## Expansion

The positive equilibrium solves $N=N/(1+\alpha+\beta N)+mN$, which gives the formula and the threshold $(1+\alpha)m>\alpha$, equivalently $p(0)+m(\tau)>1$ with $p(0)=1/(1+\alpha)$. As a function of a continuous delay $s=\tau+1$, $m=(a-be^{-Ks})e^{-Ps}$ has a single maximum where $aP=b(P+K)e^{-Ks}$, whose value is the left-hand side of the window condition; so $\{\tau:(1+\alpha)m(\tau)>\alpha\}$ is an interval around that maximizer, and $N_+^*$ is an increasing function of $m$. Global stability follows from monotonicity of the map $(N_t,N_{t-\tau})\mapsto N_{t+1}$ in each argument and a convergence theorem for higher-order monotone difference equations. Replacing Beverton–Holt by Ricker adult survival allows period-doubling (odd $\tau$) and Neimark–Sacker (even $\tau$) bifurcations.

## Sources

- C. J. Greyson-Gaito, S. H. Streipert, G. S. K. Wolkowicz, "Adding a fecundity-survival trade-off to a discrete population model with maturation delay", *Mathematical Biosciences* 400 (2026), 109767, Section 3 (model (EqT1BH)), Theorems 8, 9, 11, 12, 13, 21 and 22, <https://doi.org/10.1016/j.mbs.2026.109767> (preprint arXiv:2507.18765).
