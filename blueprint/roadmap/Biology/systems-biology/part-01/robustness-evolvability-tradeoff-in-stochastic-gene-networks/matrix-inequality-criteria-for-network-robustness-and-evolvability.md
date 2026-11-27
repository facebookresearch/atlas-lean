# Matrix inequality criteria for network robustness and evolvability

**Model.** Linearize a gene regulatory network around a target phenotype (shifted to $x_e = 0$) as $\dot x = Ax$, $x \in \mathbb R^n$. Heritable kinetic-parameter fluctuations driven by independent unit white noises $n_l(t)$, $l = 1, \dots, L$, with fluctuation matrices $A_l$, and environmental stimuli $v(t)$ entering through $B$, give the Itô system

$$dx = \big(Ax + Bv\big)\,dt + \sum_{l=1}^L A_l x\, dw_l, \qquad dw_l = n_l\, dt.$$

**Proposition 1 (genetic robustness).** If there is $P \succ 0$ with

$$PA + A^{\mathsf T}P + \sum_{l=1}^L A_l^{\mathsf T}PA_l \preceq 0,$$

then the network without stimuli ($v = 0$) is robustly (mean-square) stable at $x_e = 0$ despite the parameter fluctuations; with $A_l = 0$ this reduces to the Lyapunov inequality $PA + A^{\mathsf T}P \preceq 0$.

**Evolvability level.** For the stimulus-driven network, the attenuation level is the smallest $\rho$ such that, for zero initial state and all $v$,

$$E\int_0^{t_p} x^{\mathsf T}x\, dt \le \rho\, E\int_0^{t_p} v^{\mathsf T}v\, dt,$$

the worst-case energy ratio from environmental stimuli to phenotype deviation up to the present time $t_p$; $1/\rho$ measures environmental robustness of the phenotype.

**Proposition 3 (joint criterion).** If there is $P \succ 0$ with

$$A^{\mathsf T}P + PA + \sum_{l=1}^L A_l^{\mathsf T}PA_l + I + \tfrac1\rho PBB^{\mathsf T}P \preceq 0,$$

then the network tolerates the genetic fluctuations and attenuates environmental stimuli to level $\rho$. The best certified level is $\rho_0 = \min \rho$ subject to this inequality, which by a Schur complement is a linear matrix inequality in $(P, \rho)$.

## Expansion

For $V(x) = x^{\mathsf T}Px$, Itô's formula gives $E\,dV = E\big[x^{\mathsf T}(PA + A^{\mathsf T}P + \sum_l A_l^{\mathsf T}PA_l)x + 2x^{\mathsf T}PBv\big]dt$, the extra $A_l^{\mathsf T}PA_l$ terms being the Itô correction from multiplicative noise. Completing the square in $v$ shows that the joint inequality makes $E[V(x(t_p))] + E\int_0^{t_p}(x^{\mathsf T}x - \rho v^{\mathsf T}v)\,dt \le V(x(0))$, which is the attenuation bound. Because the fluctuation terms $A_l^{\mathsf T}PA_l$ are positive semidefinite and consume part of the stability margin of $A$, larger genetic fluctuations leave less room for the disturbance term and force a larger $\rho$: robustness to genetic variation and the capacity to respond to the environment trade off within the same Lyapunov budget.

## Sources

- B.-S. Chen, Y.-P. Lin, "On the interplay between the evolvability and network robustness in an evolutionary biological network: a systems biology approach", Evolutionary Bioinformatics (2011), Eqs 4–7, 12–13, 20–21 and Propositions 1–3, <https://doi.org/10.4137/ebo.s8123>, PMCID PMC3210637.
