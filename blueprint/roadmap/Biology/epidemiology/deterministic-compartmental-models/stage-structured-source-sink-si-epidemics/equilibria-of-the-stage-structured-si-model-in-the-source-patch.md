# Equilibria of the stage-structured SI model in the source patch

**Model.** In patch $i \in \{1,2\}$ hosts are susceptible or infected juveniles ($J_{S,i}, J_{I,i}$) and adults ($A_{S,i}, A_{I,i}$), with $N_i$ the total. Infection is lifelong (no recovery), only susceptible adults reproduce, and juveniles mature at rate $\alpha$. In the source patch,

$$\begin{aligned}
\dot J_{S,1} &= pr\Big(1 - \frac{N_1}{k}\Big)A_{S,1} - \beta_1J_{S,1}\frac{J_{I,1}+A_{I,1}}{N_1} - \alpha J_{S,1} - \mu_SJ_{S,1},\\
\dot J_{I,1} &= \beta_1J_{S,1}\frac{J_{I,1}+A_{I,1}}{N_1} - \mu_IJ_{I,1},\\
\dot A_{S,1} &= \alpha J_{S,1} - \beta_1A_{S,1}\frac{J_{I,1}+A_{I,1}}{N_1} - \mu_SA_{S,1},\\
\dot A_{I,1} &= \beta_1A_{S,1}\frac{J_{I,1}+A_{I,1}}{N_1} - \mu_IA_{I,1},
\end{aligned}$$

where $r$ is the birth rate, $k$ the carrying capacity, $p$ the fraction of offspring retained in patch $1$ (the fraction $1-p$ recruits into the sink patch $2$, which has the same structure plus this inflow), and $\mu_S, \mu_I$ the death rates of susceptible and infected hosts. Write $R_{0,i} = \beta_i/\mu_I$, $R_\alpha = \alpha/\mu_I$, $R_s = \mu_S/\mu_I$, $R_p = p/\mu_I$.

**Proposition.**
1. If $R_{0,1} < 1$, the disease-free equilibrium of patch $1$ is locally asymptotically stable (and likewise for patch $2$ with $R_{0,2}$).
2. If $R_{0,1} > 1$, any endemic equilibrium of patch $1$, with total infected $I_1^* = J_{I,1}^* + A_{I,1}^*$, has

$$J_{S,1}^* = \frac{I_1^*}{(R_{0,1}-1)(\lambda_1+1)},\quad A_{S,1}^* = \frac{\lambda_1 I_1^*}{(R_{0,1}-1)(\lambda_1+1)},\quad J_{I,1}^* = \frac{I_1^*}{\lambda_1+1},\quad A_{I,1}^* = \frac{\lambda_1 I_1^*}{\lambda_1+1},$$

with adult-to-juvenile ratio $\lambda_1 = R_\alpha/(R_{0,1} + R_s - 1)$ in both classes; in particular the prevalence is $I_1^*/N_1^* = 1 - 1/R_{0,1}$. The value of $I_1^*$ solves an explicit equation that vanishes at $R_{0,1} = 1$ and at $R_{0,1} = 1 + \tfrac{R_\alpha}{2}\big(-1 \pm \sqrt{1 + 4rR_p/R_\alpha}\big) - R_s$.
When $R_{0,1} > 1$ but this equation has no positive root, the source population is driven to the extinction equilibrium: infection-induced mortality removes the reproducing susceptible adults faster than they are replaced.

The sink patch inherits its dynamics from $A_{S,1}^*$ through recruitment; a healthy source can rescue an otherwise extinct sink when the recruitment fraction $1-p$ is large enough.

## Proof sketch

At an endemic equilibrium the infected-class equations give $\beta_1 (S/N_1) = \mu_I$ for both stages, i.e. the susceptible fraction is $1/R_{0,1}$, so $J_{S}+A_S = I^*/(R_{0,1}-1)$. The juvenile and adult equations then give the same stage ratio $\lambda_1$ among susceptibles (from $\alpha J_S = (\beta_1 I/N + \mu_S)A_S$ with $\beta_1 I/N = \mu_I(R_{0,1}-1)$) and among infecteds. Substituting into the birth equation leaves a single equation for $I_1^*$.

## Sources

- Jimmy Calvo-Monge, Jorge Arroyo-Esquivel, Alyssa Gehman and Fabio Sanchez, "Source-Sink Dynamics in a Two-Patch SI Epidemic Model with Life Stages and No Recovery from Infection", *Bulletin of Mathematical Biology* 86 (2024), 102, <https://doi.org/10.1007/s11538-024-01328-7>. Preprint version: arXiv:2402.06779 (2024), model equations, disease-free stability propositions, the endemic equilibrium proposition for patch 1 with its remark on roots, and the extinction-equilibrium discussion, <https://doi.org/10.48550/arXiv.2402.06779>.
