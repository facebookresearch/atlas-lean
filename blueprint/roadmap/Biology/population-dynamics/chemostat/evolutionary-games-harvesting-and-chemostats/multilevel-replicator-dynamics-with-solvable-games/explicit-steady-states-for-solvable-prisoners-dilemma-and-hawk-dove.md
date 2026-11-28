# Explicit long-time limits of multilevel replicator dynamics for solvable Prisoner's Dilemma and Hawk–Dove games

**Model.** A population of $M$ groups of $N$ individuals plays a symmetric two-strategy game (strategies $C$, $D$) with payoffs $R,S,T,P\ge0$ for $CC,CD,DC,DD$. Individuals reproduce within groups by a Moran process at rate $1+w_I\cdot$(payoff) and groups replicate at rate $\Lambda(1+w_G\cdot$average payoff). With $\lambda=\Lambda w_G/w_I$, taking $M\to\infty$ and then $N\to\infty$, the density $f(t,x)$ of groups with cooperator fraction $x\in[0,1]$ solves

$$\partial_tf(t,x)=-\partial_x\big[x(1-x)(\beta+\alpha x)f(t,x)\big]+\lambda f(t,x)\Big[G(x)-\int_0^1G(y)f(t,y)\,dy\Big],$$

with $\alpha=R-S-T+P$, $\beta=S-P$, $\gamma=S+T-2P$ and average group payoff $G(x)=P+\gamma x+\alpha x^2$. The **Hölder exponent** $\theta$ of the initial measure $\mu_0$ near $x=1$ is the infimum of $\Theta\ge0$ such that $\mu_0[1-x,1]/x^\Theta$ has a positive finite limit as $x\to0$. In the explicit cases treated below the dynamics preserve it; the source does not prove preservation in general and leaves that to future work.

**Theorem (Prisoner's Dilemma family).** Take $T=R+2$, $P=S+1$, i.e. payoffs $R=\gamma+P-1$, $S=P-1$, $T=\gamma+P+1$ with $\gamma>1$, so the within-group drift is $-x(1-x)(1+x)$ and $G(x)=P+\gamma x-x^2$. Let $\mu_0$ have Hölder exponent $\theta$ near $x=1$.
- If $\lambda(\gamma-1)<2\theta$, then $\mu_t\rightharpoonup\delta_0$: cooperation is lost.
- If $\lambda(\gamma-1)>2\theta$, then $\mu_t$ converges weakly to the density

$$f^\theta_\infty(x)=Z^{-1}x^{\lambda(\gamma-1)-2\theta-1}(1-x)^{\theta-1}(1+x)^{-\lambda\gamma+\theta-1}.$$

(The source's Proposition 3.2 prints the last exponent as $-\lambda\gamma/2+\theta-1$; its (3.13) and the partial fractions of $\lambda(G-c)/g$, $g=-x(1-x)(1+x)$, give the exponents $\lambda(\gamma-1)-2\theta-1$, $\theta-1$ and $-\lambda\gamma+\theta-1$.)

Moreover, for $\theta\ge1$ the modal group type of the steady state, $\hat x=\arg\sup_xf^\theta_\infty(x)$, tends, as $\lambda\to\infty$, to $\gamma-1$ when $1\le\gamma\le2$ and to $1$ when $\gamma>2$; so when the best group is mixed ($x^*=\gamma/2<1$) even arbitrarily strong group selection makes the most common group type less cooperative than the group optimum.

**Theorem (Hawk–Dove family).** Take $T=R+1$, $S=P+1$, i.e. $R=\gamma+P-2$, $S=P+1$, $T=\gamma+P-1$, so the within-group drift is $x(1-x)(1-2x)$ with interior equilibrium $x=1/2$. Let $\mu_0$ have Hölder exponents $\zeta>0$ near $0$ and $\theta$ near $1$.
- If $\lambda(\gamma-3)<2\theta$, then $\mu_t\rightharpoonup\delta_{1/2}$.
- If $\lambda(\gamma-3)>2\theta$, then $\mu_t$ converges to the density supported on $[1/2,1]$

$$f_\infty(x)=Z^{-1}(2x-1)^{\lambda(\gamma-3)-2\theta-1}(1-x)^{\theta-1}x^{-\lambda(\gamma-2)+\theta-1},\qquad x\ge\tfrac12 .$$

In both games the threshold reads $\lambda\,[G(1)-G(x_{\mathrm{eq}})]=\theta\,|g'(1)|$, where $g$ is the within-group drift and $x_{\mathrm{eq}}$ the within-group equilibrium: $G(1)-G(0)=\gamma-1$ and $|g'(1)|=2$ for the Prisoner's Dilemma, $G(1)-G(1/2)=(\gamma-3)/2$ and $|g'(1)|=1$ for Hawk–Dove.

## Expansion

For these payoff families the replicator ODE $\dot x=x(1-x)(\beta+\alpha x)$ is explicitly solvable, so the PDE can be solved by characteristics: $f(t,\cdot)$ is the pushforward of $\mu_0$ along the replicator flow, multiplied by the exponential of the accumulated relative group fitness. Near $x=1$ the flow pulls mass toward the within-group equilibrium at the exponential rate $|g'(1)|$, so the mass of near-cooperator groups decays like $e^{-\theta|g'(1)|t}$, while group replication amplifies them like $e^{\lambda[G(1)-G(x_{\mathrm{eq}})]t}$. Comparing the two exponents gives the threshold; above it the limit density is a stationary solution of the PDE.

## Sources

- Daniel B. Cooney, "The replicator dynamics for multilevel selection in evolutionary games", Journal of Mathematical Biology 79 (2019), 101–154, <https://doi.org/10.1007/s00285-019-01352-5>. Published version of arXiv:1810.12777, cited next; locators there refer to the arXiv version.
- Daniel B. Cooney, "The Replicator Dynamics for Multilevel Selection in Evolutionary Games", arXiv:1810.12777 (2018): PDE derivation (Section 2), Definition of the Hölder exponent, Propositions 3.1–3.3 (Prisoner's Dilemma), Propositions 4.1–4.2 (Hawk–Dove). <https://doi.org/10.48550/arXiv.1810.12777>
