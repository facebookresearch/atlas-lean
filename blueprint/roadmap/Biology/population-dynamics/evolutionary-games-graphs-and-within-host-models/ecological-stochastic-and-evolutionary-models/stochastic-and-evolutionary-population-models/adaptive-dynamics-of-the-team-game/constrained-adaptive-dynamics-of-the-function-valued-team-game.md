# Constrained adaptive dynamics of the function-valued team game

**Team game.** A team (species) is a function $f:[0,1]\to[0,\infty)$ with $\int_0^1f>0$, where $\int_a^bf$ is the number of individuals whose competitive ability lies in $(a,b)$. Randomly chosen individuals of two teams compete, the stronger replicates and the weaker dies, so the payoff to $f$ against $g$ is

$$E[f,g]=\int_0^1f(x)\Big(\int_0^xg(y)\,dy-\int_x^1g(y)\,dy\Big)dx,$$

a zero-sum, symmetric, bilinear game. Teams must respect the mean-competitive-ability (MCA) constraint

$$\mathrm{MCA}(f)=\frac{\int_0^1xf(x)\,dx}{\int_0^1f(x)\,dx}\le\frac12,\qquad\text{i.e.}\quad w(f):=\int_0^1\big(x-\tfrac12\big)f(x)\,dx\le0 .$$

For continuous or bounded measurable strategies, the Nash equilibria are exactly the collections of positive constant functions (one per team, not necessarily equal).

**Adaptive dynamics.** The canonical equation of adaptive dynamics for function-valued traits, with identity mutational covariance, unit prefactor, and the MCA constraint imposed by projection, is the Cauchy problem $\partial_tf=Af$, $f(0)=f_0$, where

$$Af(x)=\nabla E(f)(x)-12\,H(w(f))\,\big(x-\tfrac12\big)\int_0^1\big(y-\tfrac12\big)\nabla E(f)(y)\,dy,\qquad \nabla E(f)(x)=\int_0^xf-\int_x^1f,$$

$H$ is the Heaviside function and $12=\|x-\tfrac12\|_{L^2}^{-2}$. Thus the selection gradient $\nabla E(f)$ is used unchanged while the MCA constraint is slack, and its component normal to $\{w=0\}$ is removed once the constraint binds.

**Theorem.** Fix $1\le p\le\infty$.

1. (Spectrum) On $L^p[0,1]$, the only solutions of $Af=\lambda f$ with $f\ne0$ are constant functions, with $\lambda=0$.
2. (Stationary points are Nash equilibria) The only stationary solutions $Af=0$ in $L^p[0,1]$ are the constants; among admissible strategies, these are precisely the equilibrium strategies of the team game.
3. (Well-posedness) For every $f_0\in L^p[0,1]$ the problem has a solution $\alpha:[0,\infty)\to L^p[0,1]$. If $\int_0^1f_0\ne0$ and $\mathrm{MCA}(f_0)=\tfrac12$, then $\mathrm{MCA}(\alpha(t))=\tfrac12$ for all $t>0$; if moreover $p\ge2$, then $\|\alpha(t)\|_{L^2}$ is constant in $t$. If $f_0\in C^k[0,1]$, the solution is $C^k$ at every time.
4. (Positivity for short times) If $f_0$ is continuous or bounded measurable, admissible, and $f_0\ge K>0$, then for some $T>0$ the solution remains an admissible strategy of the same regularity class on $[0,T]$.

## Expansion

Because $E$ is bilinear and antisymmetric, the selection gradient is the linear Volterra-type operator $f\mapsto\int_0^xf-\int_x^1f$, and $A$ is linear on each of the regions $w<0$ and $w\ge0$. On each region $A$ is bounded on $L^p$ (Hölder's inequality gives a Lipschitz constant $1+12\|x-\tfrac12\|_p\|x-\tfrac12\|_q$), so Picard–Lindelöf gives global solutions. Differentiating $Af=\lambda f$ in $x$ gives $\lambda f'=2f-c$ with a constant $c$; the boundary conditions force $f$ constant and $\lambda=0$. Norm conservation on $\{w=0\}$ comes from antisymmetry: $\langle f,\nabla E(f)\rangle=E[f,f]=0$, and the projection keeps the flow tangent to the constraint. Since the equilibria are neutral (eigenvalue $0$) and the dynamics is linear, perturbations of equilibria neither grow nor shrink, and non-stationary solutions oscillate.

## Sources

- Carl-Joar Karlsson, Philip Gerlee and Julie Rowlett, "An adaptive dynamics framework for microbial ecology and evolution", Scientific Reports 15 (2025), 24307, <https://doi.org/10.1038/s41598-025-08636-5>; numbering as in arXiv:2401.17090: Theorem 2.2 (equilibria, quoted from earlier work), the constrained dynamics of Section 3.1, Theorem 3.4, Proposition 3.6, Theorem 3.8 and Theorem 3.11.
