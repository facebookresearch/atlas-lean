# Bang-bang threshold control of the stochastic SIS model

**Setting.** The infected fraction $I_t\in(0,1)$ of an endemic SIS infection with intervention $\zeta_t\in[0,\bar\zeta]$, $\bar\zeta\in(0,1]$, follows

$$dI_t=\big(\beta(1-\zeta_t)(1-I_t)I_t-\gamma I_t\big)\,dt+\sigma(1-I_t)I_t\,dW_t,$$

where the intervention reduces the contact rate and $\sigma$ models environmental noise in transmission. With running cost $C(x,\zeta)=c_1(x)+(1-x)c_2(\zeta)$ ($c_1$ penalizes prevalence, $c_2$ is the per-susceptible intervention cost), the ergodic control problem is to minimize

$$\limsup_{T\to\infty}\frac1T\,\mathbb E\Big[\int_0^TC(I_t,\zeta_t)\,dt\Big].$$

Without control, the stochastic reproduction number $R_0^S=\beta/\gamma-\sigma^2/(2\gamma)$ separates exponential extinction ($R_0^S<1$, $\sigma^2\le\beta$) from persistence with a unique stationary distribution ($R_0^S>1$), following Gray et al.

**Proposition 5.5.** For every admissible feedback control $\zeta(x)$ that does not shut transmission off near $0$ (the persistence condition), the controlled diffusion never hits $0$ or $1$ in finite time and is positive Harris recurrent on $(0,1)$.

**Theorem 3.2 (bang-bang optimality).** Under the paper's standing assumptions (A0)–(A3), including concavity of $c_2$, if the HJB equation of the ergodic problem has a solution $(\phi,\eta)$ with optimal average cost $\eta<c_2(\bar\zeta)$, then there is $x_*\in(0,1)$ such that the threshold control

$$\zeta^\star(x)=\bar\zeta\,\mathbf 1\{x\ge x_*\}$$

is optimal among all admissible feedback controls satisfying the persistence condition: no intervention below prevalence $x_*$, maximal intervention above.

**Propositions 4.1–4.2.** The optimal ergodic cost $\eta^\star$ and the cost $\eta^0$ of never intervening satisfy $|\eta^\star-\eta^0|\to0$ as $\beta$ decreases to its critical value (where $R_0^S\downarrow1$) and as $\sigma$ increases to its critical value; near the extinction threshold, intervention buys asymptotically nothing.

## Expansion

The HJB equation $\inf_{\zeta}\{b^\zeta\phi'+\tfrac12a^2\phi''+C(x,\zeta)\}=\eta$ with $b^\zeta(x)=\beta(1-\zeta)(1-x)x-\gamma x$ and $a(x)=\sigma(1-x)x$ is minimized pointwise in $\zeta$: the $\zeta$-dependent part is $(1-x)\big[c_2(\zeta)-\beta\zeta x\phi'(x)\big]$, and concavity of $c_2$ makes its minimum lie at an endpoint $\zeta\in\{0,\bar\zeta\}$. The switching set $A=\{x:\beta\bar\zeta x\phi'(x)\ge c_2(\bar\zeta)\}$ is shown to be an interval $[x_*,1]$ by matching the value functions of the two regimes at the switch point. Non-explosion uses the Lyapunov function $V_0(x)=-\log x-\log(1-x)$, whose generator is bounded by $\max\{\beta,\gamma\}+\sigma^2/2$ uniformly over controls, and positive recurrence uses the persistence condition near $0$.

## Sources

- M. Buckland, S. Christensen, P. Le Borne, C. Pokalyuk, "Optimal long-run control of endemic infections: bang-bang threshold policies in a stochastic SIS model", arXiv preprint (2026), Theorem 3.2, Propositions 4.1, 4.2 and 5.5, <https://doi.org/10.48550/arXiv.2609.05495>.
