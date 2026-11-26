# Nonequilibrium transient centers and finite-time escape criteria

**Setting.** Let $\dot x = f(x)$ on $\mathbb{R}^n$ with flow $\varphi_t$, and let $v \in C^1(\mathbb{R}^n,\mathbb{R})$ be an observable (for example, the infected population). Its speed along the flow is $g(x) = Dv(x) = \nabla v(x)\cdot f(x)$. For $s > 0$ put $T_s(\xi) = \inf\{t \ge 0 : |g(\varphi_t\xi)| > s\}$ ($\infty$ if never). A point $\xi$ is a *$(v,s,T)$-transient point* if $T < T_s(\xi) < \infty$: the observable stays $s$-slow for longer than $T$ but eventually speeds up. A point $x^*$ is a *$v$-transient center* if there is $S > 0$ such that for all $0 < s < S$, all $T > 0$ and every neighborhood $U$ of $x^*$, $U$ contains a $(v,s,T)$-transient point. Let $\Xi = \{x : g(\varphi_t x) = 0 \text{ for all } t \in \mathbb{R}\}$.

**Structure.** A $v$-transient center $x^*$ satisfies $g(x^*) = 0$; its forward orbit consists of $v$-transient centers; and it is also a $(\sigma v + \beta)$-transient center for every $\sigma \ne 0$, $\beta \in \mathbb{R}$. For $x^* \in \Xi$, $x^*$ is a $v$-transient center iff there is $S^* > 0$ such that every neighborhood of $x^*$ contains a point $\xi$ with $T_{S^*}(\xi) < \infty$.

**Theorem (exponential escape criterion).** Let $x^* \in \Xi$ and $g \in C^1$. Suppose there are an open set $W$, a continuous $\alpha : W \to \mathbb{R}$ and constants $m, S^* > 0$ such that
1. every neighborhood of $x^*$ contains $z \in W$ with $0 < |g(z)| \le S^*$;
2. if $z \in W$ and $|g(z)| \le S^*$, then $\varphi_t z \in W$ for $0 \le t < T_{S^*}(z)$;
3. for all $y \in W$ with $|g(y)| \le S^*$: $Dg(y) = \alpha(y)g(y)$ and $\alpha(y) \ge m$.

Then $x^*$ is a $v$-transient center. (Variants replace 3 by $D(g^2) \ge \chi(g^2)$ for a positive continuous $\chi$, or by an auxiliary $\Lambda$ with $\Lambda \le m$ and $D\Lambda \ge c > 0$.)

**Theorem (hyperbolic equilibria).** Let $v \in C^2$, $0$ a hyperbolic equilibrium with $A = Df(0)$ and generalized unstable eigenspace $E^u$. If $x^* \in \Xi$, $A^\top\nabla v(0) \not\perp E^u$ and $\varphi_t x^* \to 0$ as $t \to \infty$, then $0$ and $x^*$ are $v$-transient centers.

In an SIR-type model with delayed loss of stability of the disease-free state, this shows that points of the disease-free invariant set $\{I = 0\}$ near the unstable endemic-free branch are transient centers: trajectories stay near $I = 0$ for arbitrarily long before the infection resurges.

## Depends on

## Expansion

Near $x^*$ the observable speed $g$ is arbitrarily small, so trajectories started close to $x^*$ remain $s$-slow for arbitrarily long times by continuity of the flow. The issue is to show they eventually leave the slow regime; condition 3 gives $\frac{d}{dt}g(\varphi_t z) = \alpha g$ with $\alpha \ge m$, so $|g(\varphi_t z)| \ge |g(z)|e^{mt}$ while the trajectory stays in $W$, forcing $T_{S^*}(z) \le m^{-1}\log(S^*/|g(z)|) < \infty$; condition 2 keeps the trajectory in $W$ until then. At a hyperbolic equilibrium, trajectories near the stable invariant set eventually follow the unstable directions, and the transversality condition makes $g$ grow along them.

## Sources

- A. Pasion and F. Magpantay, "Nonequilibrium Transient Centers in Continuous-Time Systems", arXiv:2610.41930 (2026), Definitions 2.1–2.2, Theorems 2.3, 2.4, 3.1, 3.3, 3.4, 4.2 and 4.4, <https://doi.org/10.48550/arXiv.2610.41930>.
