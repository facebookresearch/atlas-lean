# Receptor-dependent within-host reproduction number with a CTL response

**Model.** Uninfected epithelial cells $T$, infected cells $I$, free virus $V$, surface receptor (ACE2) concentration $E$ and virus-specific CTLs $C$ satisfy

$$\begin{aligned}
T' &= \lambda_1 - \beta E V T - d_T T, &
I' &= \beta E V T - d_I I - p I C, &
V' &= m d_I I - d_V V, \\
E' &= \lambda_2 - \theta\beta E V T - d_E E, &
C' &= \alpha I C \Big(1 - \frac{C}{C_{\max}}\Big) - d_c C, & &
\end{aligned}$$

with positive parameters: infection needs a receptor, so the incidence is $\beta E V T$; each entry destroys receptor at relative rate $\theta$; an infected cell releases on average $m$ virions; CTLs kill infected cells at rate $p$ and proliferate logistically up to $C_{\max}$ in response to antigen.

**Proposition.** Let $T_0 = \lambda_1/d_T$, $E_0 = \lambda_2/d_E$ and

$$R_0 = \frac{m \beta \lambda_1 \lambda_2}{d_T d_E d_V} = \frac{m\beta T_0 E_0}{d_V}.$$

1. The infection-free equilibrium $(T_0, 0, 0, E_0, 0)$ is locally asymptotically stable if $R_0 < 1$ and unstable if $R_0 > 1$.
2. A CTL-free infected equilibrium $(\bar T, \bar I, \bar V, \bar E, 0)$ with all components positive exists if and only if $R_0 > 1$. Its receptor level is the positive root

$$\bar E = \frac{(\lambda_2 - \theta\lambda_1) + \sqrt{(\lambda_2 - \theta\lambda_1)^2 + 4 d_E \theta d_T d_V/(\beta m)}}{2 d_E},$$

and $\bar T = d_V/(\beta m \bar E)$, $\bar I = (\lambda_1 - d_T \bar T)/d_I$, $\bar V = m d_I \bar I / d_V$.
3. At this equilibrium the CTL direction has eigenvalue $\alpha \bar I - d_c$, so a CTL response can invade exactly when $\bar I > d_c/\alpha$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

At the infection-free state the infected subsystem is $I' = \beta E_0 T_0 V - d_I I$, $V' = m d_I I - d_V V$ (the CTL equation decouples with eigenvalue $-d_c$, and $T$, $E$ relax at rates $d_T$, $d_E$). Its next-generation matrix has spectral radius $\beta E_0 T_0 \cdot m d_I/(d_I d_V) = R_0$, which gives item 1. For item 2, the $I$ and $V$ equations at equilibrium give $\beta \bar E \bar V \bar T = d_I \bar I$ and $\bar T = d_V/(\beta m \bar E)$; the receptor equation becomes $\lambda_2 - \theta(\lambda_1 - d_T \bar T) - d_E \bar E = 0$, i.e. $q(\bar E) = d_E \bar E^2 - (\lambda_2 - \theta\lambda_1)\bar E - \theta d_T d_V/(\beta m) = 0$. Positivity of $\bar I$ requires $\bar E > E_c = d_T d_V/(\beta m \lambda_1)$, and since $q(E_c) = E_c (d_E E_c - \lambda_2)$, this holds iff $E_c < E_0$, iff $R_0 > 1$. Item 3 is the $(5,5)$ entry $\alpha I(1 - 2C/C_{\max}) - d_c$ of the Jacobian at $C = 0$. The source further shows a coexistence equilibrium with $I^*$ a positive root of a cubic, feasible only when $I^* > d_c/\alpha$, and gives Routh–Hurwitz conditions for the stability of both infected equilibria.

## Sources

- A. N. Chatterjee, F. Al Basir, "A model for SARS-CoV-2 infection with treatment", *Computational and Mathematical Methods in Medicine* 2020 (2020) 1352982, model (2), Section 3 (equilibria (4)–(9), $R_0$ in Eq. (14), Theorem 1, Theorems 2–3). The closed form for $\bar E$, the equivalence with $R_0 > 1$ and the CTL invasion eigenvalue are derived here; the source's printed expression for $\bar E$ contains sign errors. <https://doi.org/10.1155/2020/1352982> (PMC7463400).
