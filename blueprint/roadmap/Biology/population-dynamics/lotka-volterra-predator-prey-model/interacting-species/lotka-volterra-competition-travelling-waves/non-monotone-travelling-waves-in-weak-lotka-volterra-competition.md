# Non-monotone travelling waves in weak Lotka–Volterra competition

**Setting.** Consider the competition–diffusion system

$$u_t=u_{xx}+u(1-u-cv),\qquad v_t=dv_{xx}+v(a-bu-v),\qquad d,a,b,c>0,$$

in the strict weak-competition regime $b<a<1/c$, where the coexistence equilibrium is

$$(u^*,v^*)=\Big(\frac{1-ac}{1-bc},\ \frac{a-b}{1-bc}\Big)\in(0,\infty)^2 .$$

A travelling wave $(u,v)(\xi)$, $\xi=x+st$, solves $u''-su'+u(1-u-cv)=0$, $dv''-sv'+v(a-bu-v)=0$ with $(u,v)(-\infty)=(0,0)$ and $(u,v)(+\infty)=(u^*,v^*)$. Let $s^*=\max\{2,2\sqrt{ad}\}$.

**Proposition 1.1 (Tang–Fife; minimal speed).** For every $d>0$ and $a,b,c$ with $b<a<1/c$, a travelling wave exists if and only if $s\ge s^*$ (Theorem A.1 rules out $0<s<s^*$).

**Proposition 3.2 (monotonicity inside the box).** If a wave profile satisfies $0<u<u^*$ and $0<v<v^*$ on $\mathbb R$, it is strictly monotone.

**Theorem 1.1.** For any $d>0$, $b<a$ and $s\ge s^*$ there is $\delta(a,b,s)>0$ such that if $\delta(a,b,s)<c<1/a$, a non-monotone travelling wave exists.

**Theorem 1.2.** For any $d>0$, $a<1/c$ and $s\ge s^*$ there is $\delta(d,a,c,s)>0$ such that if $\delta(d,a,c,s)<b<a$, a non-monotone travelling wave exists.

**Theorem 1.3 (degenerate limit).** If $b<a$, $ac=1$ and $s\ge s^*$, there is a nontrivial front–pulse solution in which $u(\xi)\to0$ as $|\xi|\to\infty$; Proposition 4.1 gives the symmetric statement for $v$ when $a=b$.

## Expansion

At $ac=1$ the coexistence state collapses to $(0,a)$, so a wave from $(0,0)$ to $(u^*,v^*)$ degenerates into a front in $v$ carrying a pulse in $u$ that rises and returns to zero. Perturbing into $c<1/a$ keeps the pulse while $u^*$ becomes small but positive, so $u$ overshoots $u^*$ and the profile cannot be monotone. Existence is by super- and sub-solutions bracketing the profile between $0$ and $(u^*,v^*)$ (Proposition 3.1) combined with this continuation argument; by Proposition 3.2 a non-monotone wave must leave the box $(0,u^*)\times(0,v^*)$, and oscillation of one component near $+\infty$ forces oscillation of the other (Proposition 3.3).

## Sources

- C.-C. Chen, T.-Y. Hsiao, S.-C. Wang, "Non-Monotone Traveling Waves of the Weak Competition Lotka-Volterra System", *Discrete and Continuous Dynamical Systems - B* 37 (2026), 206–228, Propositions 1.1, 3.1–3.3, 4.1, Theorems 1.1–1.3 and A.1, <https://doi.org/10.3934/dcdsb.2026049> (preprint arXiv:2510.04501).
