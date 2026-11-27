# Steady states of a three-tiered microbial food web in the chemostat

**Model.** In a chemostat with dilution rate $D > 0$ and a single fed substrate, a first organism $x_0$ degrades substrate $s_0$ (inflow concentration $s_0^{\mathrm{in}} > 0$) into an intermediate $s_1$ while consuming hydrogen $s_2$; a second organism $x_1$ converts $s_1$ into hydrogen and is inhibited by it; a hydrogenotroph $x_2$ consumes hydrogen.

After rescaling so that all yields equal one except

$$\omega = \frac{1}{2(1 - Y_0)(1 - Y_1)},$$

where $Y_0, Y_1$ are the biomass yields of $x_0, x_1$ ($\omega$ measures the hydrogen demand of $x_0$ relative to the hydrogen supply from $x_1$), the model is

$$\dot x_0 = (\mu_0(s_0,s_2) - D - a_0)x_0,\quad \dot x_1 = (\mu_1(s_1,s_2) - D - a_1)x_1,\quad \dot x_2 = (\mu_2(s_2) - D - a_2)x_2,$$

$$\dot s_0 = D(s_0^{\mathrm{in}} - s_0) - \mu_0 x_0,\quad \dot s_1 = -Ds_1 + \mu_0 x_0 - \mu_1 x_1,\quad \dot s_2 = -Ds_2 + \mu_1 x_1 - \omega\mu_0 x_0 - \mu_2 x_2,$$

with maintenance (decay) rates $a_i \ge 0$. The growth functions are not of a specific form: they vanish when their substrate is absent, $\mu_0$ increases in $s_0$ and in $s_2$ (it needs hydrogen), $\mu_1$ increases in $s_1$ and decreases in $s_2$ (hydrogen inhibition), $\mu_2$ increases in $s_2$, and $s_2 \mapsto \mu_0(\infty, s_2)$ increases while $s_2 \mapsto \mu_1(\infty, s_2)$ decreases (Monod and inhibition-type kinetics satisfy all of this).

Let $M_0(\cdot, s_2)$, $M_1(\cdot, s_2)$, $M_2$ be the inverses of $s_0 \mapsto \mu_0$, $s_1 \mapsto \mu_1$, $s_2 \mapsto \mu_2$. On the interval of $s_2$ where both $\mu_0(\infty, s_2) > D + a_0$ and $\mu_1(\infty, s_2) > D + a_1$, define

$$\psi(s_2, D) = M_0(D + a_0, s_2) + \frac{M_1(D + a_1, s_2) + s_2}{1 - \omega},$$

assumed to have a unique interior minimum $\bar s_2(D)$ (true for Monod kinetics, where $\psi$ is convex), and put $F_1(D) = \psi(\bar s_2, D)$, $F_2(D) = \psi(M_2(D + a_2), D)$, $F_3(D) = \partial_{s_2}\psi(M_2(D + a_2), D)$.

1. **Steady states.** Solutions stay nonnegative and bounded. Besides washout $SS_1 = (0,0,0,s_0^{\mathrm{in}},0,0)$, the only possible steady states are $SS_2$ ($x_2 = 0$, the first two organisms present) and $SS_3$ (all three present). If $\omega \ge 1$, neither exists. If $\omega < 1$: $SS_2$ exists iff $s_0^{\mathrm{in}} \ge F_1(D)$, its $s_2$-component solving $\psi(s_2) = s_0^{\mathrm{in}}$ (generically two solutions $s_2^\flat < \bar s_2 < s_2^\sharp$); $SS_3$ exists iff $s_0^{\mathrm{in}} > F_2(D)$, and is then unique, with $s_2 = M_2(D + a_2)$.
2. **Stability without maintenance** ($a_0 = a_1 = a_2 = 0$). Washout is always stable. $SS_2$ is stable iff $\mu_2(s_2) < D$ and $\partial_{s_2}\psi > 0$; hence $SS_2^\flat$ is always unstable, and $SS_2^\sharp$ is stable iff $F_3(D) > 0$ and $SS_3$ does not exist. If $F_3(D) \ge 0$, $SS_3$ is stable whenever it exists; if $F_3(D) < 0$, $SS_3$ is stable iff an explicit Routh–Hurwitz quantity $F_4(D, s_0^{\mathrm{in}})$ is positive, and it can be unstable near $SS_2^\flat$.

These conditions partition the operating plane $(D, s_0^{\mathrm{in}})$ into regions of washout, two-species and three-species coexistence, with bistability between washout and coexistence where $SS_2^\sharp$ or $SS_3$ is stable.

## Depends on

- [Chemostat equilibria and the washout threshold](chemostat-equilibria-and-washout.md)

## Expansion

At a steady state with $x_0, x_1 > 0$ the growth equations force $\mu_0(s_0, s_2) = D + a_0$ and $\mu_1(s_1, s_2) = D + a_1$, so $s_0 = M_0(D + a_0, s_2)$ and $s_1 = M_1(D + a_1, s_2)$; the substrate balances then reduce to the scalar equation $\psi(s_2) = s_0^{\mathrm{in}}$ when $x_2 = 0$, and to $s_2 = M_2(D + a_2)$ with positivity of $x_2$ equivalent to $s_0^{\mathrm{in}} > \psi(M_2(D + a_2))$ when $x_2 > 0$. The factor $1/(1 - \omega)$ records that only the fraction $1 - \omega$ of produced hydrogen is available after the first organism's uptake, which is why $\omega \ge 1$ rules out coexistence. Without maintenance, total mass $s_0 + x_0 + \dots$ relaxes to the feed, reducing the system to three dimensions where the Jacobian at each steady state can be analysed: $\partial_{s_2}\psi > 0$ on the right branch makes $SS_2^\sharp$ a stable node in the two-species face, and invasion by $x_2$ is governed by the sign of $\mu_2(s_2) - D$. For $SS_3$, the sign of $F_3$ decides whether the coexistence point lies on the right branch of $\psi$, where stability is automatic, or the left one, where a Routh–Hurwitz test is needed.

## Sources

- T. Sari, M. J. Wade, "Generalised approach to modelling a three-tiered microbial food-web", *Mathematical Biosciences* (2017), Sections 2–7 (Eqs. (14)–(22), (29)–(34), (41)–(48), assumptions H1–H8, Proposition 1, Lemmas 1–4, Propositions 2–4), <https://doi.org/10.1016/j.mbs.2017.07.005> (PMC5552901).
