# Convergence of doubly parabolic Keller–Segel to the parabolic–elliptic system as $\tau\to0$

**Models.** In $\mathbb{R}^2$ consider the parabolic–elliptic system (PE) and the doubly parabolic system (PP) with parameter $\tau>0$:

$$\text{(PE)}\ \ u_t=\Delta u-\nabla\cdot(u\nabla\varphi),\ \ \Delta\varphi+u=0;\qquad \text{(PP)}\ \ u_t=\Delta u-\nabla\cdot(u\nabla\varphi),\ \ \tau\varphi_t=\Delta\varphi+u,\ \ \varphi(0)=0,$$

both with $u(0)=u_0$. Here $u$ is a cell density and $\varphi$ a chemoattractant concentration; $\tau$ measures how slowly the chemical relaxes. Define the space-time decay norm and the critical data space

$$\|u\|_{\mathcal{X}}=\operatorname*{ess\,sup}_{t>0,\,x\in\mathbb{R}^2}(t+|x|^2)\,|u(x,t)|,\qquad \|u_0\|_E=\|e^{t\Delta}u_0\|_{\mathcal{X}} .$$

$E$ contains the Dirac mass and embeds in the weak Hardy space $\mathcal{H}^1_w$, so its elements may be nonintegrable.

**Theorem.**
1. *(Global small solutions.)* There are absolute constants $\epsilon,\beta>0$ (resp. $\epsilon^*,\beta^*$) such that if $\|u_0\|_E<\epsilon$ (resp. $<\epsilon^*$), then (PE) (resp. (PP), for every $\tau>0$) has a unique global mild solution in $\mathcal{X}$ with $\|u\|_{\mathcal{X}}\le\epsilon\beta$ (resp. $\le\epsilon^*\beta^*$).
2. *(Singular limit.)* There is $\epsilon'>0$ such that if $\|u_0\|_E<\epsilon'$, the solutions $u^\tau$ of (PP) converge to the solution $u$ of (PE) in $\mathcal{X}$ as $\tau\searrow0$.
3. *(Stronger topologies.)* If moreover $u_0\in E\cap\mathcal{L}$, with $\mathcal{L}=L^1$ (with $u_0\ge0$, or $\|u_0\|_1$ small) or $\mathcal{L}$ a shift-invariant Banach space of local measures, and $\|u_0\|_E$ is small enough, then both solutions stay bounded in $\mathcal{L}$ uniformly in time and $\sup_{t>0}\|u^\tau(t)-u(t)\|_{\mathcal{L}}\to0$ as $\tau\searrow0$.
4. *(Blow-up of complex-valued solutions.)* There is a Schwartz profile $w_0$ with $\hat w_0\ge0$ and $\|\hat w_0\|_{L^1}=1$ such that for large $A$ every tempered distributional solution of (PP) with $u_0=Aw_0$ (in general complex-valued) blows up in finite time, in every homogeneous Besov norm $\dot B^{a,\infty}_\infty$.

## Expansion

Both systems are written in Duhamel form $u=e^{t\Delta}u_0-B(u,u)$: for (PE), $B_0(u,v)=\int_0^te^{(t-s)\Delta}\nabla\cdot\big(u\nabla(-\Delta)^{-1}v\big)(s)\,ds$ with the logarithmic Newtonian kernel, and for (PP), $\nabla\varphi$ is replaced by a heat-type space-time integral of $u$ with time scale $\tau$. The weight $t+|x|^2$ is invariant under the scaling $u\mapsto\lambda^2u(\lambda x,\lambda^2t)$ of both systems, and the bilinear forms are bounded on $\mathcal{X}$ uniformly in $\tau$, so a contraction argument gives small global solutions. The difference $B_\tau-B_0$ tends to zero on these solutions, but $\nabla\varphi^\tau$ is unstable as $\tau\to0$ in weighted spaces, which is why the $L^1$ and local-measure versions need separate estimates.

## Sources

- Piotr Biler and Lorenzo Brandolese, "On the parabolic-elliptic limit of the doubly parabolic Keller--Segel system modelling chemotaxis", arXiv:0804.1000 (2008), Theorems 2.1, 3.1, 4.1, 4.2 and 5.1, <https://doi.org/10.48550/arXiv.0804.1000>.
