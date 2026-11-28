# Semidefinite LaSalle principle and global convergence of the SAIR model

**Invariance principle.** Let $\dot x = f(x)$ with $f \in C^1(\mathbb{R}^n)$ and $f(x^\ast) = 0$. Let $V \in C^1(\mathbb{R}^n, \mathbb{R})$ satisfy, for some constant $c$:
1. the sublevel set $L_V(c) = \{ x : V(x) \le c \}$ is compact;
2. $V(x) \ge V(x^\ast)$ for all $x \in L_V(c)$ (positive *semi*definiteness relative to $x^\ast$; strict inequality off $x^\ast$ is not required);
3. $\dot V(x) = \nabla V(x) \cdot f(x) \le 0$ for all $x \in L_V(c)$.

**Theorem.** Let $M = \{ x \in L_V(c) : \dot V(x) = 0 \}$ and let $\Omega$ be the largest invariant set contained in $M$. Then every solution with $x(0) \in L_V(c)$ satisfies $x(t) \to \Omega$; in particular, if $\{x^\ast\}$ is the only invariant set in $M$, then $x(t) \to x^\ast$.

**SAIR model.** With population fractions $S, A, I, R$ (susceptible, asymptomatic infectious, symptomatic infectious, removed), transmission rates $\beta_A, \beta_I > 0$, recovery rates $\gamma_A, \gamma_I > 0$ and symptom-onset rate $\delta > 0$,

$$\dot S = -\beta_A A S - \beta_I I S, \qquad \dot A = \beta_A A S + \beta_I I S - (\gamma_A + \delta) A, \qquad \dot I = \delta A - \gamma_I I, \qquad \dot R = \gamma_A A + \gamma_I I .$$

The simplex $\{(S,A,I) \in \mathbb{R}^3_{\ge 0} : S + A + I \le 1\}$ is invariant and the equilibria are exactly $\{(S, 0, 0) : S \in [0,1]\}$.

**Corollary.** Every solution in the simplex converges to the disease-free set $\{A = I = 0\}$; that is, $A(t) \to 0$ and $I(t) \to 0$ as $t \to \infty$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

Since $\dot V \le 0$ on $L_V(c)$, that compact set is forward invariant, so each trajectory starting in it has a nonempty compact invariant $\omega$-limit set. $V$ is non-increasing and bounded below on $L_V(c)$, so it tends to a constant and is constant on the $\omega$-limit set, which therefore lies in $M$ and, being invariant, in $\Omega$; definiteness of $V$ was never used. For SAIR take $V = S + A + I$: then $\dot V = -(\gamma_A A + \gamma_I I) \le 0$, vanishing exactly on $\{A = I = 0\}$, which consists of equilibria and is invariant. The epidemic always burns out, and the final susceptible fraction depends on initial conditions, which is why convergence is to a set of equilibria rather than to one point. Linearizing at $(S_0, 0, 0)$ gives the reproduction number $R_0 = S_0\big(\beta_A + \beta_I\,\delta/\gamma_I\big)/(\gamma_A + \delta)$: an asymptomatic case infects at rate $\beta_A S_0$ for mean time $1/(\gamma_A + \delta)$ and becomes symptomatic with probability $\delta/(\gamma_A + \delta)$, then infects at rate $\beta_I S_0$ for mean time $1/\gamma_I$.

## Sources

- S. Ansumali, S. Kaushal, A. Kumar, M. K. Prakash and M. Vidyasagar, "Modelling a pandemic with asymptomatic patients, impact of lockdown and herd immunity, with applications to SARS-CoV-2", Annual Reviews in Control 50 (2020), 432–447, Section 3 (Eqs. (22)–(30), Theorems 5–6), <https://doi.org/10.1016/j.arcontrol.2020.10.003>, PMCID: PMC7546280.
- M. Robinson and N. I. Stilianakis, "A model for the emergence of drug resistance in the presence of asymptomatic infections", Mathematical Biosciences 243 (2013), 163–177.
