# Spreading and vanishing for chemotaxis in a time-periodic shifting habitat

**Model.** A species $u$ that produces its own chemoattractant $v$ lives on $\mathbb R$ in a habitat whose suitability moves with a time-periodic speed:

$$u_t=u_{xx}-\chi(uv_x)_x+u\bigl(r(t,x-s(t))-bu\bigr),\qquad 0=v_{xx}-\lambda v+\mu u,$$

with positive constants $\chi,b,\lambda,\mu$ and $s'(t)$ continuous and $\omega$-periodic. Assume (H1): $r$ is globally Hölder, $\omega$-periodic in $t$, nondecreasing in $\xi$, with uniform limits $r(t,-\infty)<0<r(t,\infty)$; and (H2): $b>\chi\mu$ and $b\ge\Bigl(1+\frac12\frac{(\sqrt{r^*}-\sqrt\lambda)_+}{\sqrt{r^*}+\sqrt\lambda}\Bigr)\chi\mu$. Set

$$c=\frac1\omega\int_0^\omega s'(t)\,dt,\qquad r^*=\frac1\omega\int_0^\omega r(t,\infty)\,dt,\qquad c^*=2\sqrt{r^*},$$

and let $p(t)$ be the positive $\omega$-periodic solution of $p'=p\,(r(t,\infty)-bp)$. If $\chi\mu<b$, solutions with bounded uniformly continuous nonnegative data are global and bounded.

**Theorem (compactly supported data).** Let $u_0\ge0$ have nonempty compact support.
1. If $c>c^*$ (the habitat outruns the species), then $u(t,x)\to0$ uniformly on $\mathbb R$.
2. If $-c^*\le c<c^*$, then for every $0<\varepsilon<(c^*-c)/2$, $u\to0$ uniformly on $\{x\le(c-\varepsilon)t\}$ and on $\{x\ge(c^*+\varepsilon)t\}$, while $\liminf_t\inf_{(c+\varepsilon)t\le x\le(c^*-\varepsilon)t}u>0$. If moreover $b>2\chi\mu$, then $u(t,x)-p(t)\to0$ uniformly on $(c+\varepsilon)t\le x\le(c^*-\varepsilon)t$.
3. If $c<-c^*$, then $u\to0$ on $\{x\le(-c^*-\varepsilon)t\}$ and on $\{x\ge(c^*+\varepsilon)t\}$ and stays bounded below on $(-c^*+\varepsilon)t\le x\le(c^*-\varepsilon)t$: the species spreads at the free speed $c^*$ in both directions (converging to $p(t)$ there if $b>2\chi\mu$).

**Forced waves.** If $b>(1+\bar r/\underline r)\chi\mu$ with $\bar r,\underline r$ the max and min of $r(t,\infty)$, and $c$ exceeds an explicit threshold, there is an $\omega$-periodic forced wave $(U(t,x-ct),V(t,x-ct))$ connecting $(0,0)$ to $(p(t),\frac\mu\lambda p(t))$.

## Expansion

When $\chi=0$ the problem reduces to a time-periodic Fisher–KPP equation in a shifting habitat, whose free spreading speed is $2\sqrt{r^*}$ with $r^*$ the time-averaged growth rate at the favourable end. Chemotaxis with $\chi\mu<b$ keeps solutions bounded, and the comparison arguments use sub- and supersolutions that absorb the term $\chi u v_{xx}=\chi u(\lambda v-\mu u)$. The extra condition $b>2\chi\mu$ makes the periodic state $p(t)$ globally attracting inside the occupied region.

## Sources

- Shuwen Xue and Xiao-Qiang Zhao, "Propagation dynamics of a parabolic-elliptic chemotaxis model in a time-periodic shifting environment", arXiv:2610.34753 (2026), Proposition 1.1 and Theorems 1.1–1.3, <https://doi.org/10.48550/arXiv.2610.34753>.
