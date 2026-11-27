# Equilibria and saddle-node bifurcations of the adaptive dynamics of a vaccination game

**Game.** In the Bauch–Earn vaccination game an individual vaccinates with probability $P$ while the population uptake is $p$. The payoff is

$$E(P,p)=-rP-\pi(p)\,(1-P),$$

where $0<r<1$ is the relative risk of vaccination versus infection, and $\pi(p)$ is the probability that an unvaccinated individual is eventually infected at uptake $p$: $\pi$ is smooth and non-increasing on $[0,1]$, $\pi(0)=1$, and $\pi(p)=0$ for $p\ge p^\ast$, the herd-immunity threshold. If a fraction $\epsilon\in[0,1]$ of the population plays $P$ and the rest plays $Q$, then $p=\epsilon P+(1-\epsilon)Q$, and the adaptive dynamics $\dot P=\partial_PE(P,\epsilon P+(1-\epsilon)Q)\big|_{P=Q}$ is the scalar ODE

$$\dot P=f(P):=\pi(P)-r-\epsilon\,\pi'(P)\,(1-P).$$

**Theorem.**

1. There is at least one equilibrium in $(0,p^\ast)$, since $f(0)=(1-r)-\epsilon\pi'(0)>0$ and $f(1)=-r<0$.
2. If $\pi$ is convex, there is a unique equilibrium $P_0$; it is stable (a Nash equilibrium of the game), decreasing in $r$ and increasing in $\epsilon$, and

$$P_0\in\bigl[\pi^{-1}(r),\ p^\ast\bigr).$$

(The source's upper bound also involves $(\pi')^{-1}\bigl(\frac{1-r}{\epsilon}\bigr)$, but $\pi'\le0$ never takes the positive value $\frac{1-r}{\epsilon}$, so that term is undefined and is dropped here.)

3. For general $\pi$, there is an odd number of non-degenerate equilibria, and they alternate between stable and unstable starting with a stable one at the lowest uptake.
4. As $r$ or $\epsilon$ varies, the only bifurcations are saddle-node bifurcations, creating or annihilating a stable–unstable pair. The bifurcation diagram in $r$ is the graph of $P\mapsto\pi(P)-\epsilon\pi'(P)(1-P)$ rotated by $\pi/2$ and cut off at the levels $0$ and $1$; for $r\neq0$ the diagram in $\epsilon$ is likewise the rotated graph of $P\mapsto\frac{\pi(P)-r}{\pi'(P)(1-P)}$ cut off at $0$ and $1$.

As $r\to0$ the equilibrium uptake tends to $p^\ast$ and as $r\to1$ it tends to $0$, so no bounds independent of $r$ and $\epsilon$ hold.

## Depends on

- [Fitness Gradient](../../../population-dynamics/classification-of-adaptive-dynamics-singular-str/fitness-gradient.md)

## Expansion

Equilibria solve $\pi(P)-r=\epsilon\pi'(P)(1-P)$. The left side decreases from $1-r$ at $P=0$ to $-r$ beyond $p^\ast$; the right side is non-positive and vanishes beyond $p^\ast$, so the graphs cross in $(0,p^\ast)$. Convexity of $\pi$ makes $f$ strictly decreasing ($f'=(1+\epsilon)\pi'-\epsilon\pi''(1-P)<0$ where $\pi'<0$), giving uniqueness and stability; implicit differentiation of $f(P_0;r,\epsilon)=0$ gives the monotonicity in $r$ and $\epsilon$, and evaluating the sign of $f$ at the endpoints of the stated interval localizes $P_0$. For general $\pi$, $f$ is positive at $0$ and negative at $1$, so its simple zeros alternate in the sign of $f'$, i.e. between stable and unstable, and their number is odd. Since $f$ depends affinely on $r$ (and on $\epsilon$), a parameter change can only shift the graph, so equilibria are born or destroyed in pairs at tangencies, which are saddle-node bifurcations, and solving $f=0$ for the parameter gives the bifurcation curves as rotated graphs.

## Sources

- Nataliya Balabanova, Manh Hong Duong, "Adaptive dynamics for individual payoff game-theoretic models of vaccination", arXiv (2024). Section 2 (game and adaptive dynamics), Section 3 (Theorem 3.1, Lemma 3.4), Section 4 (Observations 4.1 and 4.3, Lemmas 4.2 and 4.4). <https://doi.org/10.48550/arXiv.2411.09519>. Published version: Journal of Dynamics and Games 16(0) (2026), 15–32, <https://doi.org/10.3934/jdg.2025037>; locators above refer to the arXiv version.
