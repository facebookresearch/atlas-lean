# Reproduction number and threshold dynamics of an age-structured host–vector model

Humans are split into age classes $i \in \{J, A, S\}$ (juvenile, adult, senior) with maturation $J \to A$ at rate $\alpha$ and $A \to S$ at rate $\xi$, and each class into susceptible $S_i$, exposed $E_i$, asymptomatic $I_{Ai}$, symptomatic $I_{Si}$ and recovered $R_i$. Juveniles are recruited at rate $\pi_J$, class $i$ dies at rate $\mu_i$, exposed humans of class $i$ become infectious at rate $\sigma_i$, splitting into asymptomatic and symptomatic fractions, and recover at rates $\gamma_{Ai}, \gamma_{Si}$. Vectors are susceptible $S_M$, exposed $E_M$ or infectious $I_M$, recruited at rate $\pi_M$, dying at rate $\mu_M$ and becoming infectious at rate $\sigma_M$. With biting rate $b_M$, per-bite transmission probabilities $\beta_i$ (vector to human of class $i$) and $\beta_M$ (human to vector), and total human population $N_H$, the forces of infection are

$$\lambda_i = \frac{\beta_i b_M I_M}{N_H}, \qquad \lambda_M = \frac{\beta_M b_M \sum_{j} (I_{Aj} + I_{Sj})}{N_H}.$$

Infection classes move with their hosts on maturation. The feasible region $\Omega$ (human total at most $\pi_J/\mu_H$, vector total at most $\pi_M/\mu_M$) is positively invariant, and there is a unique disease-free equilibrium $\mathcal E_0$ with susceptible levels $S_J^*, S_A^*, S_S^*, S_M^*$.

**Theorem.**
1. (Reproduction number) With $F$ and $V$ the new-infection and transfer matrices at $\mathcal E_0$,

$$\mathcal R_0 = \rho(FV^{-1}) = \sqrt{(\mathcal R_{JM} + \mathcal R_{AM} + \mathcal R_{SM})\, \mathcal R_{MH}},$$

where $\mathcal R_{iM}$ is the expected number of infectious humans that end up in the infectious classes from infections of age class $i$ caused by one infectious vector (counting progression through later age classes), and $\mathcal R_{MH}$ is the expected number of infectious vectors produced by such human infections. $\mathcal E_0$ is locally asymptotically stable if $\mathcal R_0 < 1$ and unstable if $\mathcal R_0 > 1$.
2. (Global stability) On $\Omega_1 = \{X \in \Omega : S_J \le S_J^*, S_A \le S_A^*, S_S \le S_S^*, S_M \le S_M^*\}$, which is positively invariant, $\mathcal E_0$ is globally asymptotically stable whenever $\mathcal R_0 \le 1$.
3. (Endemic equilibrium) Without disease-induced death, the model has a unique endemic equilibrium when $\mathcal R_0 > 1$: the steady-state force of infection on juveniles solves a cubic $b_3 x^3 + b_2 x^2 + b_1 x + b_0(1 - \mathcal R_0^2) = 0$ with $b_3, b_0 > 0$.
4. (Backward bifurcation) Adding disease-induced death rates to the infectious human classes, the modified model can undergo a backward bifurcation at $\tilde{\mathcal R}_0 = 1$ (a stable endemic equilibrium coexisting with the stable disease-free equilibrium for $\tilde{\mathcal R}_0 < 1$) when the centre-manifold coefficient condition holds.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

Infection never passes human-to-human or vector-to-vector, so with infected compartments ordered as humans then vectors the matrix $FV^{-1}$ has the bipartite block form $\begin{pmatrix} 0 & K_{HM} \\ K_{MH} & 0 \end{pmatrix}$. Its spectral radius is $\sqrt{\rho(K_{HM}K_{MH})}$, and because each generation of vector infections has a single type ($E_M \to I_M$), $K_{HM} K_{MH}$ restricted to the vector type is the scalar $(\mathcal R_{JM} + \mathcal R_{AM} + \mathcal R_{SM})\mathcal R_{MH}$; the square root reflects that a full human-to-human cycle takes two generations. On $\Omega_1$ the force of infection is bounded by its value at the disease-free susceptible levels, so the infected subsystem is dominated by the linear system $\dot x \le (F - V)x$, whose solutions decay when $\rho(FV^{-1}) \le 1$; the comparison argument plus LaSalle's invariance principle give global stability. Disease-induced death makes $N_H$ fall with prevalence, which raises the per-capita biting pressure $b_M I_M/N_H$ on the remaining susceptibles; this positive feedback is the source of the backward bifurcation.

## Sources

- F. B. Agusto, S. Easley, K. Freeman, M. Thomas, "Mathematical model of three age-structured transmission dynamics of chikungunya virus", Computational and Mathematical Methods in Medicine 2016 (2016) 4320514, Section 2 (system (10)), Lemmas 1–4, Eq. (18), Theorems 5–7, <https://doi.org/10.1155/2016/4320514>, PMCID PMC4835678.
