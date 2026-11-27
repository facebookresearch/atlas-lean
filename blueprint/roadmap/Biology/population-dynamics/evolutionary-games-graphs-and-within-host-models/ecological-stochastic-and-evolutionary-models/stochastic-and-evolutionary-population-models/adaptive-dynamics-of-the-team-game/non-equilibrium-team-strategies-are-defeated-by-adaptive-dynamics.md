# Non-equilibrium team strategies are defeated by adaptive dynamics

**Setting.** In the function-valued team game, a strategy is $f:[0,1]\to[0,\infty)$ with $\int_0^1f>0$ and mean competitive ability $\mathrm{MCA}(f)=\int_0^1xf/\int_0^1f\le\tfrac12$; the payoff is $E[f,g]=\int_0^1f(x)\big(\int_0^xg-\int_x^1g\big)dx$. Let $\alpha_t$ solve the constrained adaptive dynamics $\dot\alpha=A\alpha$, $\alpha_0=f_0$, where $A$ is the selection gradient $\nabla E(f)(x)=\int_0^xf-\int_x^1f$ with its component along $x-\tfrac12$ removed whenever $\mathrm{MCA}(f)\ge\tfrac12$.

**Theorem.**

1. (MCA drift) If $\int_0^1\alpha_t\ne0$ and $\mathrm{MCA}(\alpha_t)=\tfrac12$, then $\frac{d}{dt}\mathrm{MCA}(\alpha_t)=0$. If $0<\mathrm{MCA}(\alpha_t)<\tfrac12$ and $\alpha_t>0$, then $\mathrm{MCA}(\alpha_t)$ is increasing, with

    $$\frac{d}{dt}\mathrm{MCA}(\alpha_t)>2\Big(\tfrac12-\mathrm{MCA}(\alpha_t)\Big)^2 .$$

2. (Invasion of non-constant residents) If $f_0$ is nonnegative, bounded, measurable and not constant, then for all sufficiently small $t>0$, $E[\alpha_t,f_0]>0$: the evolved strategy defeats the initial one.
3. (Consequence) If moreover $f_0\ge K>0$, the evolved strategy is still an admissible strategy for small $t$, so adaptive dynamics produces an admissible strategy that defeats any non-constant positive $f_0$. Only the constant (equilibrium) strategies are not displaced this way, and a non-constant initial condition with $\mathrm{MCA}(f_0)=\tfrac12$ never reaches a constant function in finite time.

Without the lower bound $f_0\ge K$, the flow can leave the strategy space at once; for instance, for $f_0(x)=1-x/r$ on $[0,r]$ and $a(x-r)$ on $[r,1]$ with $\tfrac12<r<1$ and $a$ chosen so that $\mathrm{MCA}(f_0)=\tfrac12$, the constrained gradient is negative at $x=r$, where $f_0(r)=0$.

## Depends on

- [Constrained adaptive dynamics of the function-valued team game](constrained-adaptive-dynamics-of-the-function-valued-team-game.md)

## Expansion

By bilinearity, $\frac{d}{dt}E[\alpha_t,f_0]=E[A\alpha_t,f_0]$. When the MCA constraint is slack, $A=\nabla E$, and an integration by parts gives $E[\nabla E(\alpha_t),f_0]=\langle\nabla E(\alpha_t),\nabla E(f_0)\rangle$, which at $t=0$ is $\|\nabla E(f_0)\|^2>0$ unless $\nabla E(f_0)\equiv0$, i.e. unless $f_0=0$; since $E[f_0,f_0]=0$, the payoff becomes positive. On the boundary $\mathrm{MCA}=\tfrac12$, the derivative at $t=0$ is $\langle A f_0,\nabla E(f_0)\rangle=\|\nabla E(f_0)\|^2-\langle x-\tfrac12,\nabla E(f_0)\rangle^2/\|x-\tfrac12\|^2\ge0$ by Cauchy–Schwarz, with equality only if $\nabla E(f_0)$ is proportional to $x-\tfrac12$, which forces $f_0$ constant. The MCA bound follows from $\int_0^1\nabla E(f)=2(\tfrac12-\mathrm{MCA}(f))\int_0^1f$ and the analogous moment identity. Time reversal from the uniform equilibrium shows that there are admissible strategies with $\mathrm{MCA}<\tfrac12$ that evolve to the equilibrium in finite time.

## Sources

- Carl-Joar Karlsson, Philip Gerlee and Julie Rowlett, "An adaptive dynamics framework for microbial ecology and evolution", Scientific Reports 15 (2025), 24307, <https://doi.org/10.1038/s41598-025-08636-5>; numbering as in arXiv:2401.17090: Lemma 3.7, Lemma 3.9, Proposition 3.10, Theorem 3.11, Corollary 3.12 and Section 3.5.
