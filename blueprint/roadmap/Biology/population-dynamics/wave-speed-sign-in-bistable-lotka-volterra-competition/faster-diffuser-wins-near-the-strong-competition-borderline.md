# Faster diffuser wins near the strong-competition borderline

**Setting.** For the Lotka–Volterra competition–diffusion system with diffusion rate $1$ for $u$ and $d$ for $v$, growth rates $1$ and $r$, and equal competition coefficient $k>1$ (strong competition, bistable), a travelling wave $(u,v)(x-st)$ solves

$$u''+su'+u(1-u)-kuv=0,\qquad dv''+sv'+rv(1-v)-kuv=0,\qquad (u,v)(-\infty)=(0,1),\ (u,v)(+\infty)=(1,0),$$

with a unique speed $s=s(d,r,k)$. The sign of $s$ decides the winner: $s>0$ means $v$ invades the region occupied by $u$. The speed is strictly increasing in $r\in(0,k)$, and there is a unique $r_c\in(0,k)$ with $s=0$.

**Minimax characterization (prior result).** With

$$R_H(u)=\frac{k\,uH(u)+dH'(u)\,u\,[1-u-kH(u)]+2dH''(u)\int_0^u t\,[1-t-kH(t)]\,dt}{H(u)(1-H(u))}$$

over an admissible class $\Lambda$ of profiles $H$, $r_c=\inf_{H\in\Lambda}\sup_{u\in(0,1)}R_H(u)=\sup_{H\in\Lambda}\inf_{u\in(0,1)}R_H(u)$.

**Theorems.** Let $d>1$ ($v$ diffuses faster) and $k=1+\theta$.
1. As $k\to1^+$, the wave satisfies $\sup_\xi|u+v-1|\to0$ and the critical growth ratio $r_c(k)\to1$.
2. There is $c_T>0$ such that $s(d,1,k)>0$ for $1<k<1+c_T\frac{d-1}{d^4}$: with identical growth rates, the faster diffuser wins.
3. There are $c_L,c_U>0$ such that $1-c_L\frac{d-1}{d}\theta\le r_c\le1-c_U\frac{d-1}{d}\theta$ for $0<\theta\le c_T\frac{d-1}{d^4}$: the faster diffuser can even afford a growth-rate disadvantage of order $\theta(d-1)/d$.

The key constant is $\sigma_0(d)=-\int_0^1\frac{s(1-s)(2s-1)}{(d-1)s+1}\,ds>0$ for $d>1$.

## Expansion

Near $k=1$ the wave degenerates: $u+v\approx1$, and the system reduces to a scalar equation for $u$ whose bistable nonlinearity is a small perturbation of order $\theta$, so $s$ is $O(\theta)$ and its sign is governed by a solvability integral. Writing $v\approx1-u$ and rescaling, the analysis leads to a leading-order profile governed by an effective diffusivity of the form $(d-1)u+1$, and the solvability condition produces the integral $\sigma_0(d)$, whose positivity for $d>1$ gives $s>0$. Inserting a test function built from this asymptotic profile into the minimax formula yields the two-sided bounds on $r_c$.

## Sources

- C.-C. Chen, S.-C. Wang, "Propagating Direction Near the Strong-Competition Borderline in the Two-Species Lotka-Volterra Model", arXiv:2607.03066 (2026), Section 1 (system, Proposition 1.1, Theorem 1.1, Corollary 1.1), Theorems 1.2–1.4, Proposition 3.1, <https://doi.org/10.48550/arXiv.2607.03066>.
