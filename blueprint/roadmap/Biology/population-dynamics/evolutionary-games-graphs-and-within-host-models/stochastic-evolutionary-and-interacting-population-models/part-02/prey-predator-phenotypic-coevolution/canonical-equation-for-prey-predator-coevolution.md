# Canonical equation for prey–predator coevolution

Work in the prey–predator community of [Global stability of multitype Lotka–Volterra prey–predator equilibria](global-stability-of-multitype-lotka-volterra-prey-predator-equilibria.md), now with mutations: a prey of trait $x$ produces a mutant offspring with probability $u_Kp(x)$, of trait $x + \ell$ with $\ell\sim\pi(x,\ell)\,d\ell$, and a predator of trait $y$ with probability $u_KP(y)$, of trait $y + v$ with $v\sim\Pi(y,v)\,dv$. For a resident equilibrium $\mathbf z^\ast = (n^\ast,h^\ast)$ define the invasion fitnesses

$$s(x';\mathbf z^\ast) = b(x') - d(x') - \sum_i c(x',x_i)n^\ast_i - \sum_l B(x',y_l)h^\ast_l, \qquad F(y';\mathbf z^\ast) = r\sum_i B(x_i,y')n^\ast_i - D(y').$$

**Theorem.**

1. (Polymorphic evolution sequence.) Assume Assumptions A and B of that page; that for almost every trait vector the prey competition matrix $C$ satisfies $C + C^T$ positive definite and every subsystem of each LVP system is non-degenerate (Assumption C); that for every LVP equilibrium the zero sets $\{x' : s(x';\mathbf z^\ast) = 0\}$ and $\{y' : F(y';\mathbf z^\ast) = 0\}$ are Lebesgue-null (Assumption D); that the mutation densities are dominated by integrable functions, $\pi(x,u)\le\bar m(u)$ and $\Pi(y,v)\le\bar M(v)$ with $\int\bar m < \infty$, $\int\bar M < \infty$ (condition (23)); and that the initial community converges in probability to the equilibrium $\mathbf z^\ast$ of its LVP system. If $\log K \ll 1/(Ku_K) \ll e^{VK}$ for all $V > 0$, then on the time scale $t/(Ku_K)$ the community converges, in the sense of finite-dimensional distributions (for the total variation topology on measures), to a pure-jump process on equilibria of LVP systems: a mutant prey $x'$ (or predator $y'$) arises at rate proportional to the resident's equilibrium size times its reproduction, invades with probability equal to its positive invasion fitness ($[s(x';\mathbf z^\ast)]_+$, resp. $[F(y';\mathbf z^\ast)]_+$) divided by its birth rate in the resident community, and the community jumps to the globally stable equilibrium of the enlarged system.
2. (Canonical equations.) Assume further that every prey–predator pair $(x,y)$ coexists at the equilibrium $n^\ast(x,y) = \frac{D(y)}{rB(x,y)}$, $h^\ast(x,y) = \frac{1}{B(x,y)}\big(b(x) - d(x) - c(x,x)\frac{D(y)}{rB(x,y)}\big)$ (i.e. $\frac{b(x)-d(x)}{c(x,x)} > \frac{D(y)}{rB(x,y)}$), that invasion of a prey mutant implies fixation, that the mutation kernels are Lipschitz, and that the functions $g$ and $G$ below are continuous and $C^1$ in their first variable (Assumption E). Let

$$g(x';(x,y)) = p(x)\,n^\ast(x,y)\,b(x)\,\frac{s(x';(x,y))}{b(x')}, \qquad G(y';(x,y)) = P(y)\,h^\ast(x,y)\,B(x,y)\,\frac{F(y';(x,y))}{B(x,y')}.$$

If mutation steps are scaled by $\varepsilon$ and the initial traits $(X_\varepsilon(0),Y_\varepsilon(0))$ are bounded in $L^2$ and converge in law to $(x_0,y_0)$, the monomorphic trait process $(X_\varepsilon(t/\varepsilon^2), Y_\varepsilon(t/\varepsilon^2))$ converges in law on every $[0,T]$ to the unique solution of

$$\dot x = \int u\,\big[u\cdot\nabla_1 g(x;(x,y))\big]_+\,\pi(x,u)\,du, \qquad \dot y = \int v\,\big[v\cdot\nabla_1 G(y;(x,y))\big]_+\,\Pi(y,v)\,dv.$$

For symmetric mutation kernels with covariances $\gamma$ and $\Gamma$ this reduces to $\dot x = \tfrac12\gamma\nabla_1 g$, $\dot y = \tfrac12\Gamma\nabla_1 G$: prey and predator traits climb their own fitness gradients, coupled through the shared equilibrium.

## Depends on

- [Global stability of multitype Lotka–Volterra prey–predator equilibria](global-stability-of-multitype-lotka-volterra-prey-predator-equilibria.md)
- [Fitness Gradient](../../../../classification-of-adaptive-dynamics-singular-str/fitness-gradient.md)

## Expansion

Rare mutations separate time scales: between mutations the population relaxes to the globally stable LVP equilibrium (time $O(\log K)$) and stays there exponentially long, so a mutant meets a resident community at equilibrium. Its early dynamics is a branching process with growth rate given by its invasion fitness, so it invades with probability $[s]_+/b$. Global stability of the enlarged LVP system determines the new resident community. With small mutation steps and invasion implying fixation, the community stays monomorphic, each jump moves a trait by $O(\varepsilon)$ with rate proportional to $[g]_+$ or $[G]_+$, which is $O(\varepsilon)$ near the resident trait since $s(x;(x,y)) = 0$; accelerating time by $\varepsilon^{-2}$ yields a deterministic drift equal to the first moment of the jumps.

## Sources

- Manon Costa, Céline Hauzy, Nicolas Loeuille, Sylvie Méléard, "Stochastic eco-evolutionary model of a prey-predator community", arXiv (2014). Section 5 (rare mutations, Theorem 5.3; small mutations, Assumption on coexistence and invasion-implies-fixation, Theorem 5.5). <https://doi.org/10.48550/arXiv.1407.3069>. Published version: Journal of Mathematical Biology 72(3) (2016), 573–622, <https://doi.org/10.1007/s00285-015-0895-y>; locators above refer to the arXiv version.
