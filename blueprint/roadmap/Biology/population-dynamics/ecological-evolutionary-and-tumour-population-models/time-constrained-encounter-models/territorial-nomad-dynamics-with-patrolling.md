# Territorial–nomad population dynamics with a patrolling trade-off

Let $x \ge 0$ be the density of **nomads** and $y \ge 0$ the density of **territorials**, both per territory. When $y > 1$, $\min(1, y)$ territorials hold territories (**owners**) and $y - \min(1,y)$ are **intruders**. Each time an owner reconsiders its behaviour it chooses to patrol with probability $p$ and to hunt otherwise; patrolling makes it more likely to win fights (probability $\alpha_a$ versus $\alpha_r$). The decision probability $p$ is not the stationary share $\pi$ of owners that are patrolling, which is given below: for example $p = 1/2$, $\lambda_i = 0$ and $\lambda_h t_h = 1$ give $\pi = 1/3$. Write $\lambda_h, i_h, t_h$ for the prey encounter rate, intake and handling time, $b$ for the baseline intake from holding a territory, and $c_w, t_w$ and $c_l, t_l$ for the fight costs and waiting times of the winner and of the loser of a fight. The winner holds the territory after the fight and the loser becomes an intruder, so these are post-fight roles, not necessarily the pre-fight owner and intruder. Nomads that meet an owner flee, at cost $c_f$ and time $t_f$. With unit encounter rate $f$, the per-capita rate at which an owner meets active intruders is $\lambda_i = f\rho_i[y - \min(1,y)]$, and an intruder or nomad meets active owners at rate $\lambda_o = f\rho_o\min(1,y)$. The active fractions $\rho_a, \rho_r, \rho_o, \rho_i$ and the patroller share $\pi$ are given by [the time-constrained encounter formulas](intake-rate-and-active-fraction.md), for example $\rho_i = 1/(1 + \lambda_o t_l + \lambda_h t_h)$.

The ecological dynamics are

$$\dot x = x F(x,y), \qquad \dot y = y G(x,y),$$

$$G(x,y) = -d - c_{nt}x - c_{tt}y + D(y), \qquad F(x,y) = -d - c_{nn}x - c_{tn}y + \frac{\lambda_h i_h - \lambda_o c_f}{1 + \lambda_o t_f + \lambda_h t_h},$$

where $d$ is the maintenance (background death) rate, the $c$ terms are density-dependent indirect competition, and the direct-interaction fitness of an average territorial is

$$D(y) = \begin{cases} b + (1-\pi)\dfrac{\lambda_h i_h}{1 + \lambda_h t_h}, & y \le 1,\\[2ex] \dfrac1y\Big[b - f(y-1)\rho_i\rho_o(c_w + c_l) + (1-\pi)\rho_r\lambda_h i_h + (y-1)\rho_i\lambda_h i_h\Big], & y > 1.\end{cases}$$

For $y > 1$, $D(y)$ is the territory benefit, minus the cost of fights for territories, plus the hunting income of hunting owners and of intruders, averaged over the $y$ territorials per territory. The paper studies equilibria of this system for a fixed strategy $p$, gives exact parameter sets with a stable interior equilibrium and with ecological tristability, and then finds the evolutionarily stable patrolling strategy $p$ at the interior equilibrium (Sections 3–4). Depending on the territory value $b$, that strategy can be pure hunting, mixed or pure patrolling.

## Depends on

- [Intake rate and active fraction in time-constrained encounter models](intake-rate-and-active-fraction.md)

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Expansion

Encounters run on a fast time scale relative to births and deaths, so each type's fitness is its long-run intake rate at fixed $(x, y)$. Since the winner of a fight is an owner afterwards and the loser an intruder, the owner terms carry the winner's cost and time and the intruder terms the loser's. The owner terms are $D_a = b - \lambda_i c_w/(1 + \lambda_i t_w)$ for patrollers and $D_r = b + (\lambda_h i_h - \lambda_i c_w)/(1 + \lambda_i t_w + \lambda_h t_h)$ for hunters, and the intruder term $D_i$ comes from the same intake-rate formula. A territorial is an owner with probability $\min(1,y)/y$, so $D(y) = \{\min(1,y)[\pi D_a + (1-\pi)D_r] + (y - \min(1,y))D_i\}/y$. Substituting the rates gives the case formula. Because fights are counted symmetrically, $f\rho_i\cdot\rho_o$ appears with the combined cost $c_w + c_l$. For $y \le 1$ there are no intruders, so $\lambda_i = 0$.

## Sources

- T. Varga, J. Garay, J. Rychtář and M. Broom, "A temporal model of territorial defence with antagonistic interactions", *Theoretical Population Biology* (2020), <https://doi.org/10.1016/j.tpb.2020.03.005>, Sections 2.3–2.4, Equations (2.6)–(2.13), and Sections 2.5, 3 and 4 (examples, Nash equilibria and evolutionary stability).
