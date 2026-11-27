# Global dynamics of an avian–human influenza model with psychological effect

**Model.** Birds are susceptible $S_a$ or infective $I_a$; humans are susceptible $S_h$, infective $I_h$ or recovered $R_h$. Infection spreads bird-to-bird with saturating incidence and bird-to-human with a nonmonotone incidence that decreases in human prevalence (people avoid contact when many are ill); there is no human-to-human transmission:

$$\begin{aligned}
\dot S_a &= \Pi_a - \mu_a S_a - \frac{\beta_a I_a S_a}{1 + bI_a}, & \dot I_a &= \frac{\beta_a I_a S_a}{1 + bI_a} - (\mu_a + \delta_a) I_a,\\
\dot S_h &= \Pi_h - \mu_h S_h - \frac{\beta_h I_a S_h}{1 + cI_h^2}, & \dot I_h &= \frac{\beta_h I_a S_h}{1 + cI_h^2} - (\mu_h + \delta_h + \gamma) I_h, \qquad \dot R_h = \gamma I_h - \mu_h R_h,
\end{aligned}$$

with $b, c \ge 0$ and all other parameters positive.

**Theorem.** Let $R_0 = \dfrac{\beta_a \Pi_a}{\mu_a(\mu_a + \delta_a)}$, the spectral radius of the next-generation matrix (which is lower triangular, so humans, being dead-end hosts, do not contribute).

1. If $R_0 \le 1$, the only equilibrium is disease-free, $A = (\Pi_a/\mu_a, 0, \Pi_h/\mu_h, 0, 0)$, and it is globally asymptotically stable.

2. If $R_0 > 1$, there is a unique endemic equilibrium with $I_a^{\ast\ast} = \dfrac{\mu_a(R_0 - 1)}{\mu_a b + \beta_a}$, $S_a^{\ast\ast} = (\mu_a + \delta_a)(1 + bI_a^{\ast\ast})/\beta_a$, $I_h^{\ast\ast}$ the unique positive root of

    $$g(I_h) = \mu_h(\mu_h + \delta_h + \gamma)\, c\, I_h^3 + (\mu_h + \delta_h + \gamma)(\mu_h + \beta_h I_a^{\ast\ast})\, I_h - \Pi_h \beta_h I_a^{\ast\ast},$$

    $S_h^{\ast\ast} = (\mu_h + \delta_h + \gamma) I_h^{\ast\ast}(1 + cI_h^{\ast\ast2})/(\beta_h I_a^{\ast\ast})$ and $R_h^{\ast\ast} = \gamma I_h^{\ast\ast}/\mu_h$; it is globally asymptotically stable for positive initial conditions, and the disease-free equilibrium is unstable.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Semidefinite LaSalle principle and global convergence of the SAIR model](../sair-model-with-asymptomatic-transmission/semidefinite-lasalle-principle-and-global-convergence-of-the-sair-model.md)

## Expansion

The bird subsystem is autonomous. For $R_0 \le 1$ the Volterra-type function $V = S_a - S_a^\ast - S_a^\ast\ln(S_a/S_a^\ast) + I_a$ gives $\dot V \le -\mu_a (S_a - S_a^\ast)^2/S_a + (\mu_a + \delta_a)(R_0 - 1)I_a \le 0$, using $1/(1 + bI_a) \le 1$, and LaSalle's principle yields convergence to $(S_a^\ast, 0)$. For $R_0 > 1$ the Dulac function $B_1 = (1 + bI_a)/(\beta_a I_a S_a)$ makes the divergence of $B_1\cdot(\dot S_a, \dot I_a)$ equal to $-\Pi_a(1 + bI_a)/(\beta_a I_a S_a^2) - b(\mu_a + \delta_a)/(\beta_a S_a) < 0$, excluding periodic orbits, so the locally stable endemic point attracts all positive solutions in the plane (Poincaré–Bendixson). The human subsystem, with $I_a$ at its limit, is again planar: $g$ is strictly increasing with $g(0) < 0$, so the equilibrium is unique, and the Dulac function $B_2 = (1 + cI_h^2)/(\beta_h S_h I_a^{\ast\ast})$ gives negative divergence $-\Pi_h(1 + cI_h^2)/(\beta_h I_a^{\ast\ast} S_h^2) - (1 + 3cI_h^2)(\mu_h + \delta_h + \gamma)/(\beta_h S_h I_a^{\ast\ast})$; the theory of asymptotically autonomous systems transfers the limits to the full model. The psychological factor $1/(1 + cI_h^2)$ therefore lowers human prevalence (larger $c$ gives smaller $I_h^{\ast\ast}$) but cannot affect whether the infection persists, which is decided entirely in the reservoir.

## Sources

- S. Liu, L. Pang, S. Ruan and X. Zhang, "Global dynamics of avian influenza epidemic models with psychological effect", Computational and Mathematical Methods in Medicine 2015 (2015), 913726, Sections 2–4 (Eqs. (3)–(27), Lemmas 1–3, Theorem 5, Corollary 6), <https://doi.org/10.1155/2015/913726>, PMCID: PMC4377454.
